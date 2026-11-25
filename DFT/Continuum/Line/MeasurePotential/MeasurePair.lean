/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureNEL

/-!
# The pair-density operator for smooth states

For a state `X` and `f ∈ C¹([0, 1])`, multiplying by the symmetric one-body function
`F_f(x) = Σ_k f(x_k)` gives a mixed density

`ρ̂(X, F_f X) = f ρ̂_X + T_X f`,

where `T_X f(t) = N ∫ X(t, y)² Σ_j f(y_j) dy` is the pair-density operator (**`rhoHat2_FF`**, for
continuous symmetric `X`). This is step (C) of the general interacting Hohenberg–Kohn argument
(see the formalization log).

* `FF`, `mem_FF_mul`: `F_f Φ` is again an `H¹₀` state.
* `integral_sym_xk`: for symmetric `G`, `∫ g(x_k) G = ∫ g(x₀) G`.
* `TX`, `TXP`; **`rhoHat2_FF`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-- The symmetric one-body function `F_f(x) = Σ_k f(x_k)`. -/
noncomputable def FF (f : ℝ → ℝ) (x : Cfg n) : ℝ := ∑ k, f (x k)

lemma FF_pm (f : ℝ → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : FF f (pm σ x) = FF f x := by
  simp only [FF, pm_apply]
  exact Equiv.sum_comp σ fun k => f (x k)

lemma contDiff_FF {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (FF (n := n) f) :=
  ContDiff.sum fun k _ => hf.comp (by fun_prop : ContDiff ℝ 1 fun x : Cfg n => x k)

lemma FF_cons (f : ℝ → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    FF f (Fin.cons t y : Cfg n) = f t + ∑ j, f (y j) := by
  simp [FF, Fin.sum_univ_succ]

/-- `F_f Φ` is an `H¹₀` state of the same symmetry. -/
lemma mem_FF_mul {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    (fun x => FF f x * Φ x) ∈ DomW τ n := by
  have hF := contDiff_FF (n := n) hf
  refine ⟨memLp_mul_cont hF.continuous hΦ.1, fun k => ⟨_, (dW_spec (hΦ.2.1 k)).mul_C1 hΦ.1 hF⟩,
    fun σ _ => ?_⟩
  filter_upwards [hΦ.2.2 σ trivial] with x hx
  simp only [FF_pm, hx]; ring

/-- For a symmetric `G`, `∫ g(x_k) G = ∫ g(x₀) G`. -/
lemma integral_sym_xk {G : Cfg n → ℝ} (hG : ∀ σ x, G (pm σ x) = G x) (g : ℝ → ℝ)
    (k : Fin (n + 1)) : ∫ x, g (x k) * G x ∂μN n = ∫ x, g (x 0) * G x ∂μN n := by
  rw [← integral_pm (Equiv.swap 0 k) (fun x => g (x 0) * G x)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [pm_apply, Equiv.swap_apply_left, hG]

/-- The pair-density operator `T_X f(t) = N ∫ X(t, y)² Σ_j f(y_j) dy`. -/
noncomputable def TX (X : Cfg n → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (n + 1) * ∫ y in Cube' n, X (Fin.cons t y) ^ 2 * ∑ j, f (y j)

lemma continuous_TX {X : Cfg n → ℝ} (hX : Continuous X) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (TX X f) := by
  refine continuous_const.mul (continuous_integral_cube' ?_)
  exact ((hX.comp continuous_cons_pair).pow 2).mul
    (continuous_finsetSum _ fun j _ => hf.comp ((continuous_apply j).comp continuous_snd))

/-- `T_X f` as a continuous function on `[0, 1]`. -/
noncomputable def TXP {X : Cfg n → ℝ} (hX : Continuous X) {f : ℝ → ℝ} (hf : Continuous f) : Pot :=
  ⟨fun t => TX X f t, (continuous_TX hX hf).comp continuous_subtype_val⟩

/-- `f` as a continuous function on `[0, 1]`. -/
noncomputable def fP {f : ℝ → ℝ} (hf : Continuous f) : Pot :=
  ⟨fun t => f t, hf.comp continuous_subtype_val⟩

lemma ext_fP {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ext (fP hf) t = f t := by
  simp [Box.ext, fP, projIcc_of_mem _ ht]

lemma ext_TXP {X : Cfg n → ℝ} (hX : Continuous X) {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ext (TXP hX hf) t = TX X f t := by
  simp [Box.ext, TXP, projIcc_of_mem _ ht]

lemma ae_cube_x0 : ∀ᵐ x ∂μN n, x 0 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [ae_cube] with x hx
  exact Ioo_subset_Icc_self (hx 0 trivial)

/-- **The mixed density with `F_f X`**: `ρ̂(X, F_f X) = f ρ̂_X + T_X f` for a continuous state
`X ∈ H¹₀` with `X² ∘ σ = X²`. -/
theorem rhoHat2_FF (hw : Continuous w) {X : Cfg n → ℝ} (hX : X ∈ DomW τ n) (hXc : Continuous X)
    (hXs : ∀ σ x, X (pm σ x) ^ 2 = X x ^ 2) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    rhoHat2 τ X (fun x => FF f x * X x) =
      fP hf.continuous * rhoHat τ X + TXP hXc hf.continuous := by
  have hfc := hf.continuous
  refine pot_eq_of_integral fun v => ?_
  have hv := continuous_ext v
  -- the left side, reduced to the first particle
  rw [int_rhoHat2 hw hX (mem_FF_mul hX hf)]
  have hG : ∀ σ x, (X (pm σ x) * (FF f (pm σ x) * X (pm σ x))) = X x * (FF f x * X x) :=
    fun σ x => by rw [FF_pm]; linear_combination (FF f x) * hXs σ x
  have hcont : Continuous fun x : Cfg n => X x * (FF f x * X x) :=
    hXc.mul ((contDiff_FF hf).continuous.mul hXc)
  have hL : pf (settingW τ n w hw) v X (fun x => FF f x * X x) =
      (n + 1) * ∫ x, ext v (x 0) * (X x * (FF f x * X x)) ∂μN n := by
    change ∫ x, LN n v x * (X x * (FF f x * X x)) ∂μN n = _
    rw [integral_LN_mul v hcont]
    simp only [integral_sym_xk (G := fun x => X x * (FF f x * X x)) hG (ext v), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  rw [hL]
  -- the right side
  have hR1 : ∫ t, ext v t * ext (fP hfc * rhoHat τ X) t ∂μ1 =
      (n + 1) * ∫ x, ext v (x 0) * (f (x 0) * (X x * X x)) ∂μN n := by
    have e : ∀ t, ext v t * ext (fP hfc * rhoHat τ X) t = ext (v * fP hfc) t * ext (rhoHat τ X) t :=
      fun t => by simp only [Box.ext, ContinuousMap.mul_apply]; ring
    simp only [e]
    rw [int_rhoHat hw hX]
    change ∫ x, LN n (v * fP hfc) x * (X x * X x) ∂μN n = _
    have hc2 : Continuous fun x : Cfg n => X x * X x := hXc.mul hXc
    rw [integral_LN_mul _ hc2]
    have hG2 : ∀ σ x, X (pm σ x) * X (pm σ x) = X x * X x := fun σ x => by
      linear_combination hXs σ x
    simp only [integral_sym_xk (G := fun x => X x * X x) hG2 (ext (v * fP hfc)), Finset.sum_const,
      Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_cube_x0] with x hx
    simp only [Box.ext, ContinuousMap.mul_apply] at *
    rw [show (fP hfc) (projIcc 0 1 zero_le_one (x 0)) = f (x 0) by
      simp [fP, projIcc_of_mem _ hx]]
    ring
  have hR2 : ∫ t, ext v t * ext (TXP hXc hfc) t ∂μ1 =
      (n + 1) * ∫ x, ext v (x 0) * (X x ^ 2 * ∑ j : Fin n, f (x j.succ)) ∂μN n := by
    have hc3 : Continuous fun x : Cfg n => ext v (x 0) * (X x ^ 2 * ∑ j : Fin n, f (x j.succ)) :=
      (hv.comp (continuous_apply 0)).mul ((hXc.pow 2).mul
        (continuous_finsetSum _ fun j _ => hfc.comp (continuous_apply _)))
    rw [integral_cube_cons hc3, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [ext_TXP hXc hfc (Ioo_subset_Icc_self ht), TX, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul]
    congr 1; funext y
    simp only [Fin.cons_zero, Fin.cons_succ]; ring
  have hsplit : ∫ t, ext v t * ext (fP hfc * rhoHat τ X + TXP hXc hfc) t ∂μ1 =
      ∫ t, ext v t * ext (fP hfc * rhoHat τ X) t ∂μ1 + ∫ t, ext v t * ext (TXP hXc hfc) t ∂μ1 := by
    have := int_ext_add_smul v (fP hfc * rhoHat τ X) (TXP hXc hfc) 1 1
    simpa using this
  rw [hsplit, hR1, hR2, ← mul_add]
  have i1 : Integrable (fun x : Cfg n => ext v (x 0) * (f (x 0) * (X x * X x))) (μN n) :=
    integrableN ((hv.comp (continuous_apply 0)).mul ((hfc.comp (continuous_apply 0)).mul
      (hXc.mul hXc)))
  have i2 : Integrable (fun x : Cfg n => ext v (x 0) * (X x ^ 2 * ∑ j : Fin n, f (x j.succ)))
      (μN n) :=
    integrableN ((hv.comp (continuous_apply 0)).mul ((hXc.pow 2).mul
      (continuous_finsetSum _ fun j _ => hfc.comp (continuous_apply _))))
  rw [← integral_add i1 i2]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [FF, Fin.sum_univ_succ]
  ring

/-! ### The continuous density of a continuous state -/

/-- For a continuous state, `ρ̂_X(t) = N ∫ X(t, y)² dy` at every `t ∈ [0, 1]`. -/
theorem rhoHat_eq_marg (hw : Continuous w) {X : Cfg n → ℝ} (hX : X ∈ DomW τ n)
    (hXc : Continuous X) (hXs : ∀ σ x, X (pm σ x) ^ 2 = X x ^ 2) (t : Icc (0 : ℝ) 1) :
    rhoHat τ X t = (n + 1) * ∫ y in Cube' n, X (Fin.cons (t : ℝ) y) ^ 2 := by
  have hc : Continuous fun s : ℝ => (n + 1) * ∫ y in Cube' n, X (Fin.cons s y) ^ 2 :=
    continuous_const.mul (continuous_integral_cube' ((hXc.comp continuous_cons_pair).pow 2))
  set p : Pot := ⟨fun s => (n + 1) * ∫ y in Cube' n, X (Fin.cons (s : ℝ) y) ^ 2,
    hc.comp continuous_subtype_val⟩
  have hp : rhoHat τ X = p := by
    refine pot_eq_of_integral fun v => ?_
    have hv := continuous_ext v
    rw [int_rhoHat hw hX]
    change ∫ x, LN n v x * (X x * X x) ∂μN n = _
    have hc2 : Continuous fun x : Cfg n => X x * X x := hXc.mul hXc
    have hG2 : ∀ σ x, X (pm σ x) * X (pm σ x) = X x * X x := fun σ x => by
      linear_combination hXs σ x
    rw [integral_LN_mul v hc2]
    simp only [integral_sym_xk (G := fun x => X x * X x) hG2 (ext v), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hc3 : Continuous fun x : Cfg n => ext v (x 0) * (X x * X x) :=
      (hv.comp (continuous_apply 0)).mul hc2
    rw [integral_cube_cons hc3]
    push_cast
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hsI := Ioo_subset_Icc_self hs
    simp only [Box.ext, projIcc_of_mem _ hsI, p, ContinuousMap.coe_mk, Fin.cons_zero]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext y; ring
  rw [hp]; rfl

/-! ### Fubini: the pair-density operator against a measure -/

section fubini

variable {m : ℕ}

instance isFiniteMeasure_cube' : IsFiniteMeasure (volume.restrict (Cube' m)) :=
  isFiniteMeasure_restrict.2 (by rw [volume_cube']; exact ENNReal.one_ne_top)

/-- `h_j(t, u) = ∫ X(t, (z with u in slot j))² dz`. -/
noncomputable def hP (X : Cfg (m + 1) → ℝ) (j : Fin (m + 1)) (t u : ℝ) : ℝ :=
  ∫ z in Cube' m, X (Fin.cons t (Fin.insertNth j u z)) ^ 2

lemma continuous_hP {X : Cfg (m + 1) → ℝ} (hX : Continuous X) (j : Fin (m + 1)) :
    Continuous fun p : ℝ × ℝ => hP X j p.1 p.2 := by
  have hae : Cube' m =ᵐ[volume] Icc (0 : Fin m → ℝ) 1 :=
    Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ)) (f := 0) (g := 1)
  have e : ∀ p : ℝ × ℝ, hP X j p.1 p.2 =
      ∫ z in Icc (0 : Fin m → ℝ) 1, X (Fin.cons p.1 (Fin.insertNth j p.2 z)) ^ 2 :=
    fun p => setIntegral_congr_set hae
  simp only [e]
  exact continuous_parametric_integral_of_continuous
    (f := fun (p : ℝ × ℝ) (z : Fin m → ℝ) => X (Fin.cons p.1 (Fin.insertNth j p.2 z)) ^ 2)
    (by fun_prop) isCompact_Icc

/-- `hP X j · u` is continuous in the first variable. -/
lemma continuous_hP_left {X : Cfg (m + 1) → ℝ} (hX : Continuous X) (j : Fin (m + 1)) (u : ℝ) :
    Continuous fun t => hP X j t u :=
  (continuous_hP hX j).comp (f := fun t : ℝ => (t, u)) (continuous_id.prodMk continuous_const)

lemma abs_hP_le {X : Cfg (m + 1) → ℝ} {C : ℝ} (hC : ∀ x, |X x| ≤ C) (j : Fin (m + 1)) (t u : ℝ) :
    |hP X j t u| ≤ C ^ 2 := by
  rw [hP, ← Real.norm_eq_abs]
  calc ‖∫ z in Cube' m, X (Fin.cons t (Fin.insertNth j u z)) ^ 2‖
      ≤ C ^ 2 * (volume.restrict (Cube' m)).real univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun z => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 2)
    _ = C ^ 2 := by simp [measureReal_def, volume_cube']

/-- The density of `T_X` against `ρ`: `r(u) = N Σ_j ∫ h_j(t, u) dρ(t)`. -/
noncomputable def rX (ρ : Measure ℝ) (X : Cfg (m + 1) → ℝ) (u : ℝ) : ℝ :=
  ((m + 1 : ℕ) + 1) * ∑ j, ∫ t, hP X j t u ∂ρ

lemma integrable_bdd_cont {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ a, |F a| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun a => by
    rw [Real.norm_eq_abs]; exact hC a)

/-- `T_X f(t) = N Σ_j ∫ f(u) h_j(t, u) du`. -/
lemma TX_eq {X : Cfg (m + 1) → ℝ} (hX : Continuous X) {CX : ℝ} (hCX : ∀ x, |X x| ≤ CX)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf : ℝ} (hCf : ∀ t, |f t| ≤ Cf) (t : ℝ) :
    TX X f t = ((m + 1 : ℕ) + 1) * ∑ j, ∫ u in Ioo (0 : ℝ) 1, f u * hP X j t u := by
  rw [TX]
  congr 1
  have hint : ∀ j : Fin (m + 1), IntegrableOn (fun y : Fin (m + 1) → ℝ =>
      X (Fin.cons t y) ^ 2 * f (y j)) (Cube' (m + 1)) := fun j =>
    integrableOn_cube' (by fun_prop)
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : Continuous fun y : Cfg m => X (Fin.cons t y) ^ 2 * f (y j) := by fun_prop
  change ∫ y, X (Fin.cons t y) ^ 2 * f (y j) ∂μN m = _
  rw [integral_cube_insertNth hc j]
  simp only [Fin.insertNth_apply_same]
  -- swap the two integrals
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX 0)
  have hF : Integrable (Function.uncurry fun (z : Fin m → ℝ) (u : ℝ) =>
      X (Fin.cons t (Fin.insertNth j u z)) ^ 2 * f u)
      ((volume.restrict (Cube' m)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    integrable_bdd_cont (C := CX ^ 2 * Cf) (by fun_prop) fun p => by
      simp only [Function.uncurry, abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hCX _) 2) (hCf _) (abs_nonneg _)
        (by positivity)
  rw [integral_integral_swap hF]
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  rw [hP, ← integral_const_mul]
  congr 1; funext z; ring

/-- **Fubini for the pair-density operator**: `∫ T_X f dρ = ∫ f r`. -/
theorem intCLM_TXP (ρ : Measure ℝ) [IsMeas01 ρ] {X : Cfg (m + 1) → ℝ} (hX : Continuous X)
    {CX : ℝ} (hCX : ∀ x, |X x| ≤ CX) {f : ℝ → ℝ} (hf : Continuous f) {Cf : ℝ}
    (hCf : ∀ t, |f t| ≤ Cf) :
    intCLM ρ (TXP hX hf) = ∫ u, f u * rX ρ X u ∂μ1 := by
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX 0)
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  rw [intCLM_apply]
  rw [integral_congr_ae ((IsMeas01.ae_mem ρ).mono fun t ht => by
    rw [ext_TXP hX hf ht, TX_eq hX hCX hf hCf t])]
  -- the integrand `f(u) h_j(t, u)` on `ρ × du`
  have hFj : ∀ j : Fin (m + 1), Integrable (fun p : ℝ × ℝ => f p.2 * hP X j p.1 p.2)
      (ρ.prod μ1) := fun j =>
    integrable_bdd_cont (C := Cf * CX ^ 2) ((hf.comp continuous_snd).mul (continuous_hP hX j))
      fun p => by
        rw [abs_mul]
        exact mul_le_mul (hCf _) (abs_hP_le hCX j _ _) (abs_nonneg _) hCf0
  have hin : ∀ j : Fin (m + 1), Integrable (fun t => ∫ u, f u * hP X j t u ∂μ1) ρ := fun j =>
    (hFj j).integral_prod_left
  rw [integral_const_mul, integral_finsetSum _ fun j _ => hin j]
  have hsw : ∀ j : Fin (m + 1), ∫ t, ∫ u, f u * hP X j t u ∂μ1 ∂ρ =
      ∫ u, ∫ t, f u * hP X j t u ∂ρ ∂μ1 := fun j =>
    integral_integral_swap (f := fun t u => f u * hP X j t u) (hFj j)
  simp only [hsw]
  have hout : ∀ j : Fin (m + 1), Integrable (fun u => ∫ t, f u * hP X j t u ∂ρ) μ1 := fun j =>
    (hFj j).integral_prod_right
  rw [← integral_finsetSum _ fun j _ => hout j, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [rX, integral_const_mul, Finset.mul_sum]
  ring_nf

/-- `∫ |h_j(t, ·) - h'_j(t, ·)| ≤ ∫ |X² - X'²|(t, y) dy`. -/
lemma integral_abs_hP_sub_le {X X' : Cfg (m + 1) → ℝ} (hX : Continuous X) (hX' : Continuous X')
    {CX : ℝ} (hCX : ∀ x, |X x| ≤ CX) (hCX' : ∀ x, |X' x| ≤ CX) (j : Fin (m + 1)) (t : ℝ) :
    ∫ u, |hP X j t u - hP X' j t u| ∂μ1 ≤
      ∫ y in Cube' (m + 1), |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| := by
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX 0)
  have hpt : ∀ u, |hP X j t u - hP X' j t u| ≤
      ∫ z in Cube' m, |X (Fin.cons t (Fin.insertNth j u z)) ^ 2 -
        X' (Fin.cons t (Fin.insertNth j u z)) ^ 2| := fun u => by
    rw [hP, hP, ← integral_sub (integrableOn_cube' (by fun_prop))
      (integrableOn_cube' (by fun_prop))]
    exact abs_integral_le_integral_abs
  have hc : Continuous fun y : Cfg m => |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| := by
    fun_prop
  have hF : Integrable (Function.uncurry fun (z : Fin m → ℝ) (u : ℝ) =>
      |X (Fin.cons t (Fin.insertNth j u z)) ^ 2 - X' (Fin.cons t (Fin.insertNth j u z)) ^ 2|)
      ((volume.restrict (Cube' m)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    integrable_bdd_cont (C := 2 * CX ^ 2) (by fun_prop) fun p => by
      simp only [Function.uncurry, abs_abs]
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hCX (Fin.cons t (Fin.insertNth j p.2 p.1))) 2
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hCX' (Fin.cons t (Fin.insertNth j p.2 p.1))) 2
      rw [sq_abs] at h1 h2
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X (Fin.cons t (Fin.insertNth j p.2 p.1))),
        sq_nonneg (X' (Fin.cons t (Fin.insertNth j p.2 p.1)))]
  have hR : ∫ y in Cube' (m + 1), |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| =
      ∫ u in Ioo (0 : ℝ) 1, ∫ z in Cube' m, |X (Fin.cons t (Fin.insertNth j u z)) ^ 2 -
        X' (Fin.cons t (Fin.insertNth j u z)) ^ 2| := by
    change ∫ y, |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| ∂μN m = _
    rw [integral_cube_insertNth hc j, integral_integral_swap hF]
  rw [hR]
  have hi1 : Integrable (fun u => |hP X j t u - hP X' j t u|) μ1 :=
    integrable_bdd_cont (C := 2 * CX ^ 2) (by
      have h1 := continuous_hP hX j; have h2 := continuous_hP hX' j
      exact ((h1.comp (Continuous.prodMk continuous_const continuous_id)).sub
        (h2.comp (Continuous.prodMk continuous_const continuous_id))).abs) fun u => by
      rw [abs_abs]
      have h1 := abs_hP_le hCX j t u; have h2 := abs_hP_le hCX' j t u
      calc |hP X j t u - hP X' j t u| ≤ |hP X j t u| + |hP X' j t u| := abs_sub _ _
        _ ≤ 2 * CX ^ 2 := by linarith
  exact integral_mono hi1 hF.integral_prod_right hpt

/-- **The densities of nearby states are `L¹`-close**:
`∫ |r_X - r_{X'}| ≤ N n ρ([0,1]) sup_t ∫ |X² - X'²|(t, y) dy`. -/
theorem integral_abs_rX_sub_le (ρ : Measure ℝ) [IsMeas01 ρ] {X X' : Cfg (m + 1) → ℝ}
    (hX : Continuous X) (hX' : Continuous X') {CX : ℝ} (hCX : ∀ x, |X x| ≤ CX)
    (hCX' : ∀ x, |X' x| ≤ CX) {K : ℝ}
    (hK : ∀ t ∈ Icc (0 : ℝ) 1,
      ∫ y in Cube' (m + 1), |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| ≤ K) :
    ∫ u, |rX ρ X u - rX ρ X' u| ∂μ1 ≤ ((m + 1 : ℕ) + 1) * (m + 1) * (ρ.real univ * K) := by
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX 0)
  set N : ℝ := (m + 1 : ℕ) + 1
  have hN : 0 ≤ N := by positivity
  have hD : ∀ j : Fin (m + 1), Integrable (fun p : ℝ × ℝ => |hP X j p.1 p.2 - hP X' j p.1 p.2|)
      (ρ.prod μ1) := fun j =>
    integrable_bdd_cont (C := 2 * CX ^ 2) ((continuous_hP hX j).sub (continuous_hP hX' j)).abs
      fun p => by
        rw [abs_abs]
        have h1 := abs_hP_le hCX j p.1 p.2; have h2 := abs_hP_le hCX' j p.1 p.2
        calc _ ≤ |hP X j p.1 p.2| + |hP X' j p.1 p.2| := abs_sub _ _
          _ ≤ 2 * CX ^ 2 := by linarith
  have hd : ∀ j : Fin (m + 1), Integrable (fun p : ℝ × ℝ => hP X j p.1 p.2 - hP X' j p.1 p.2)
      (ρ.prod μ1) := fun j =>
    integrable_bdd_cont (C := 2 * CX ^ 2) ((continuous_hP hX j).sub (continuous_hP hX' j))
      fun p => by
        have h1 := abs_hP_le hCX j p.1 p.2; have h2 := abs_hP_le hCX' j p.1 p.2
        calc _ ≤ |hP X j p.1 p.2| + |hP X' j p.1 p.2| := abs_sub _ _
          _ ≤ 2 * CX ^ 2 := by linarith
  -- pointwise bound
  have hpt : ∀ u, |rX ρ X u - rX ρ X' u| ≤
      N * ∑ j, ∫ t, |hP X j t u - hP X' j t u| ∂ρ := fun u => by
    have hiX : ∀ j : Fin (m + 1), Integrable (fun t => hP X j t u) ρ := fun j =>
      integrable_bdd_cont (C := CX ^ 2) (continuous_hP_left hX j u) fun t => abs_hP_le hCX j t u
    have hiX' : ∀ j : Fin (m + 1), Integrable (fun t => hP X' j t u) ρ := fun j =>
      integrable_bdd_cont (C := CX ^ 2) (continuous_hP_left hX' j u) fun t => abs_hP_le hCX' j t u
    rw [rX, rX, ← mul_sub, abs_mul, abs_of_nonneg hN, ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) hN
    rw [← integral_sub (hiX j) (hiX' j)]
    exact abs_integral_le_integral_abs
  have hi : Integrable (fun u => N * ∑ j, ∫ t, |hP X j t u - hP X' j t u| ∂ρ) μ1 :=
    (integrable_finsetSum _ fun j _ => (hD j).integral_prod_right).const_mul N
  have hir : Integrable (fun u => |rX ρ X u - rX ρ X' u|) μ1 :=
    hi.mono' (by
      have : AEStronglyMeasurable (fun u => rX ρ X u - rX ρ X' u) μ1 := by
        have h1 : Integrable (fun u => ∑ j, ∫ t, (hP X j t u - hP X' j t u) ∂ρ) μ1 :=
          integrable_finsetSum _ fun j _ => (hd j).integral_prod_right
        refine ((h1.const_mul N).aestronglyMeasurable).congr (ae_of_all _ fun u => ?_)
        have hiX : ∀ j : Fin (m + 1), Integrable (fun t => hP X j t u) ρ := fun j =>
          integrable_bdd_cont (C := CX ^ 2) (continuous_hP_left hX j u) fun t => abs_hP_le hCX j t u
        have hiX' : ∀ j : Fin (m + 1), Integrable (fun t => hP X' j t u) ρ := fun j =>
          integrable_bdd_cont (C := CX ^ 2) (continuous_hP_left hX' j u) fun t => abs_hP_le hCX' j t u
        simp only [rX, ← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun j _ => integral_sub (hiX j) (hiX' j)
      exact this.norm) (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_abs]; exact hpt u)
  calc ∫ u, |rX ρ X u - rX ρ X' u| ∂μ1
      ≤ ∫ u, N * ∑ j, ∫ t, |hP X j t u - hP X' j t u| ∂ρ ∂μ1 := integral_mono hir hi hpt
    _ = N * ∑ j, ∫ t, ∫ u, |hP X j t u - hP X' j t u| ∂μ1 ∂ρ := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ => (hD j).integral_prod_right]
        congr 1
        exact Finset.sum_congr rfl fun j _ =>
          (integral_integral_swap (f := fun t u => |hP X j t u - hP X' j t u|) (hD j)).symm
    _ ≤ N * ∑ _j : Fin (m + 1), ∫ _t, K ∂ρ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hN
        refine integral_mono_ae (hD j).integral_prod_left (integrable_const K) ?_
        filter_upwards [IsMeas01.ae_mem ρ] with t ht
        exact (integral_abs_hP_sub_le hX hX' hCX hCX' j t).trans (hK t ht)
    _ = N * (m + 1) * (ρ.real univ * K) := by
        simp only [integral_const, smul_eq_mul, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end fubini

end DFT.Continuum.Line
