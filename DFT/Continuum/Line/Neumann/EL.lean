/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.NEL
import DFT.Continuum.Line.Neumann.Chain
import DFT.Continuum.Line.Neumann.NGS

/-!
# The Euler–Lagrange equation with Neumann walls and `H⁻¹` potentials

* `evE_inj`, `eq_of_int`: an element of `H1E` is determined by its integrals against continuous
  functions.
* `int_rhoN_N`: `∫ u ρ_Φ = ∫ Σ_k u(x_k) Φ²` for Neumann states; `int_rhoE`.
* `rhoE2`: the mixed density `ρ(Φ, Ψ) ∈ H1E`, by polarisation; `rhoE_expand`, `rhoE_smul`.
* `kinN2`, `kinN_expand`; `QNH_expand`, `QNH_smul`, `QNH_null`, `EN_mul_leH`.
* **`euler_lagrangeNH`**: `Σ_k ∫ ∂ₖΦ ∂ₖΨ + ∫ w Φ Ψ + v(ρ(Φ, Ψ)) = E ∫ Φ Ψ` for all Neumann `Ψ`.
* `rhoE_abs`, **`isGSNH_abs`**: for bosons `|Φ|` is a ground state whenever `Φ` is.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-! ### Elements of `H1E` are determined by their integrals -/

lemma evE_inj {e e' : H1E} (h : evE e = evE e') : e = e' := by
  have hc : toE (h1N_fnE e) = toE (h1N_fnE e') := toE_congr _ _ fun t ht => by
    have := congrArg (fun P : C01 => P ⟨t, ht⟩) h
    simpa only [evE_apply] using this
  simpa only [toE_fnE] using hc

lemma eq_of_int {e e' : H1E}
    (h : ∀ u : C01, ∫ t, iccExt u t * iccExt (evE e) t ∂vol01 = ∫ t, iccExt u t * iccExt (evE e') t ∂vol01) :
    e = e' :=
  evE_inj (pot_eq_of_integral h)

lemma int_ext_evE_add_smul (u : C01) (e e' : H1E) (a b : ℝ) :
    ∫ t, iccExt u t * iccExt (evE (a • e + b • e')) t ∂vol01 =
      a * ∫ t, iccExt u t * iccExt (evE e) t ∂vol01 + b * ∫ t, iccExt u t * iccExt (evE e') t ∂vol01 := by
  rw [map_add, map_smul, map_smul, int_ext_add_smul]

/-! ### The density through its integrals -/

/-- `rhoN` has the integrals `∫ Σ_k u(x_k) Φ²` for Neumann states. -/
theorem int_rhoN_N {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (v : C01) :
    ∫ t, iccExt v t * rhoN Φ t ∂vol01 = ∫ x, (∑ k, iccExt v (x k)) * (Φ x * Φ x) ∂μN n := by
  have hv := continuous_iccExt v
  have hsq : Integrable (fun x => Φ x * Φ x) (μN n) := int_mul_L2 hΦ.1 hΦ.1
  have hint : ∀ k : Fin (n + 1), Integrable (fun x => iccExt v (x k) * (Φ x * Φ x)) (μN n) := by
    intro k
    obtain ⟨C, hC⟩ := ae_bound_cont (n := n) (hv.comp (continuous_apply k))
    exact hsq.bdd_mul (hv.comp (continuous_apply k)).aestronglyMeasurable hC
  have swapsq : ∀ k : Fin (n + 1), ∫ x, iccExt v (x k) * (Φ x * Φ x) ∂μN n =
      ∫ x, iccExt v (x 0) * (Φ x * Φ x) ∂μN n := by
    intro k
    rw [← integral_pm (Equiv.swap 0 k) (fun x => iccExt v (x 0) * (Φ x * Φ x))]
    refine integral_congr_ae ?_
    filter_upwards [hΦ.2.2 (Equiv.swap 0 k) trivial] with x hx
    simp only [pm, Equiv.swap_apply_left] at hx ⊢
    rw [hx]
    have := ch_mul_self τ (Equiv.swap 0 k)
    linear_combination (-(iccExt v (x k) * (Φ x * Φ x))) * this
  have hpt : (fun x : Cfg n => (∑ k, iccExt v (x k)) * (Φ x * Φ x)) =
      fun x => ∑ k, iccExt v (x k) * (Φ x * Φ x) := by
    funext x; rw [Finset.sum_mul]
  rw [hpt, integral_finsetSum (f := fun k x => iccExt v (x k) * (Φ x * Φ x)) _ fun k _ => hint k]
  simp only [swapsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_cube_cons' (hint 0), ← integral_const_mul]
  refine (setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_).symm
  simp only [Fin.cons_zero, rhoN, marg, ← integral_const_mul]
  push_cast
  congr 1; funext y; ring

/-- The one-body form `∫ Σ_k u(x_k) Φ Ψ`. -/
noncomputable def pfN (u : C01) (Φ Ψ : Cfg n → ℝ) : ℝ :=
  ∫ x, (∑ k, iccExt u (x k)) * (Φ x * Ψ x) ∂μN n

lemma integrable_pfN (u : C01) {Φ Ψ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n))
    (hΨ : MemLp Ψ 2 (μN n)) : Integrable (fun x => (∑ k, iccExt u (x k)) * (Φ x * Ψ x)) (μN n) := by
  have hc : Continuous fun x : Cfg n => ∑ k, iccExt u (x k) :=
    continuous_finsetSum _ fun k _ => (continuous_iccExt u).comp (continuous_apply k)
  obtain ⟨C, hC⟩ := ae_bound_cont (n := n) hc
  exact (int_mul_L2 hΦ hΨ).bdd_mul hc.aestronglyMeasurable hC

lemma pfN_expand (u : C01) {Φ Ψ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n))
    (s : ℝ) : pfN u (Φ + s • Ψ) (Φ + s • Ψ) = pfN u Φ Φ + 2 * s * pfN u Φ Ψ + s ^ 2 * pfN u Ψ Ψ :=
  integral_expand (integrable_pfN u hΦ hΦ) (integrable_pfN u hΦ hΨ) (integrable_pfN u hΨ hΨ) s

/-- `rhoE` has the integrals of the density. -/
lemma int_rhoE {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (u : C01) :
    ∫ t, iccExt u t * iccExt (evE (rhoE τ Φ)) t ∂vol01 = pfN u Φ Φ := by
  rw [pfN, ← int_rhoN_N hΦ u]
  refine integral_congr_ae ?_
  filter_upwards [(gNH_spec hΦ).2.1, ae_restrict_mem measurableSet_Ioo] with t h1 ht
  have htI := Ioo_subset_Icc_self ht
  rw [ext_evE htI, rhoE, sqE, fnE_toE _ htI, ← sq, h1]

variable (τ) in
/-- The mixed density `ρ(Φ, Ψ) = (ρ(Φ + Ψ) - ρ(Φ - Ψ)) / 4` as an element of `H1E`. -/
noncomputable def rhoE2 (Φ Ψ : Cfg n → ℝ) : H1E :=
  (1 / 4 : ℝ) • (rhoE τ (Φ + Ψ) - rhoE τ (Φ - Ψ))

lemma int_rhoE2 {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (hΨ : Ψ ∈ DomN τ n) (u : C01) :
    ∫ t, iccExt u t * iccExt (evE (rhoE2 τ Φ Ψ)) t ∂vol01 = pfN u Φ Ψ := by
  have e : rhoE2 τ Φ Ψ = (1 / 4 : ℝ) • rhoE τ (Φ + Ψ) + (-(1 / 4) : ℝ) • rhoE τ (Φ - Ψ) := by
    rw [rhoE2, smul_sub, sub_eq_add_neg, neg_smul]
  rw [e, int_ext_evE_add_smul, int_rhoE (add_mem hΦ hΨ), int_rhoE (sub_mem hΦ hΨ)]
  have h1 := pfN_expand u hΦ.1 hΨ.1 1
  have h2 := pfN_expand u hΦ.1 hΨ.1 (-1)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at h1 h2
  rw [h1, h2]; ring

/-- **`ρ(Φ + sΨ) = ρ(Φ) + 2s ρ(Φ, Ψ) + s² ρ(Ψ)`** in `H1E`. -/
lemma rhoE_expand {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (hΨ : Ψ ∈ DomN τ n) (s : ℝ) :
    rhoE τ (Φ + s • Ψ) = rhoE τ Φ + (2 * s) • rhoE2 τ Φ Ψ + (s ^ 2) • rhoE τ Ψ := by
  refine eq_of_int fun u => ?_
  have hsΨ : s • Ψ ∈ DomN τ n := Submodule.smul_mem _ s hΨ
  rw [int_rhoE (add_mem hΦ hsΨ), pfN_expand u hΦ.1 hΨ.1 s]
  rw [show rhoE τ Φ + (2 * s) • rhoE2 τ Φ Ψ + s ^ 2 • rhoE τ Ψ =
      (1 : ℝ) • ((1 : ℝ) • rhoE τ Φ + (2 * s) • rhoE2 τ Φ Ψ) + (s ^ 2) • rhoE τ Ψ by
    simp, int_ext_evE_add_smul, int_ext_evE_add_smul, int_rhoE hΦ, int_rhoE2 hΦ hΨ,
    int_rhoE hΨ]
  ring

lemma rhoE_smul {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN τ n) (c : ℝ) :
    rhoE τ (c • Ψ) = c ^ 2 • rhoE τ Ψ := by
  have h := rhoE_expand (Φ := (0 : Cfg n → ℝ)) (zero_mem _) hΨ c
  have h0 : rhoE τ (0 : Cfg n → ℝ) = 0 := by
    refine eq_of_int fun u => ?_
    rw [int_rhoE (zero_mem _)]
    simp [pfN, SturmLiouville.iccExt]
  have h2 : rhoE2 τ (0 : Cfg n → ℝ) Ψ = 0 := by
    refine eq_of_int fun u => ?_
    rw [int_rhoE2 (zero_mem _) hΨ]
    simp [pfN, SturmLiouville.iccExt]
  rw [zero_add, h0, h2] at h
  simpa using h

/-- On null states the density vanishes. -/
lemma rhoE_null {χ : Cfg n → ℝ} (hχ : χ ∈ DomN τ n) (h0 : ∫ x, χ x ^ 2 ∂μN n = 0) :
    rhoE τ χ = 0 := by
  have hzz : (fun x => χ x * χ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (χ x)) (int_mul_L2 hχ.1 hχ.1)).1
      (by rw [← h0]; simp only [sq])
  refine eq_of_int fun u => ?_
  rw [int_rhoE hχ, pfN]
  rw [integral_congr_ae (hzz.mono fun x hx => by simp only [hx, Pi.zero_apply, mul_zero] :
    (fun x => (∑ k, iccExt u (x k)) * (χ x * χ x)) =ᵐ[μN n] fun _ => (0 : ℝ))]
  simp [SturmLiouville.iccExt]

/-! ### The kinetic form -/

/-- The kinetic form `Σ_k ∫ ∂ₖΦ ∂ₖΨ` with Neumann walls. -/
noncomputable def kinN2 (Φ Ψ : Cfg n → ℝ) : ℝ := ∑ k, ∫ x, dWN k Φ x * dWN k Ψ x ∂μN n

lemma dWN_add_smul {Φ Ψ : Cfg n → ℝ} (hΦ : H1NW Φ) (hΨ : H1NW Ψ) (s : ℝ) (k : Fin (n + 1)) :
    dWN k (Φ + s • Ψ) =ᵐ[μN n] fun x => dWN k Φ x + s * dWN k Ψ x :=
  dWN_ae_eq (IsWDN.add hΦ.1 (hΨ.1.const_mul s) (dWN_spec (hΦ.2 k))
    ((dWN_spec (hΨ.2 k)).const_mul s))

lemma kinN_expand {Φ Ψ : Cfg n → ℝ} (hΦ : H1NW Φ) (hΨ : H1NW Ψ) (s : ℝ) :
    kinN (Φ + s • Ψ) = kinN Φ + 2 * s * kinN2 Φ Ψ + s ^ 2 * kinN Ψ := by
  have hk : ∀ k, ∫ x, dWN k (Φ + s • Ψ) x * dWN k (Φ + s • Ψ) x ∂μN n =
      ∫ x, dWN k Φ x * dWN k Φ x ∂μN n + 2 * s * ∫ x, dWN k Φ x * dWN k Ψ x ∂μN n +
        s ^ 2 * ∫ x, dWN k Ψ x * dWN k Ψ x ∂μN n := fun k => by
    have hA := memLp_dWN hΦ k
    have hB := memLp_dWN hΨ k
    have e := integral_expand (μ := μN n) (g := fun _ => (1 : ℝ)) (ψ := dWN k Φ)
      (φ := dWN k Ψ) (by simpa using int_mul_L2 hA hA) (by simpa using int_mul_L2 hA hB)
      (by simpa using int_mul_L2 hB hB) s
    simp only [one_mul] at e
    rw [← e]
    refine integral_congr_ae ?_
    filter_upwards [dWN_add_smul hΦ hΨ s k] with x hx
    rw [hx]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [kinN, kinN2, hk, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### Expansion of the energy -/

lemma integrable_w_mul (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n))
    (hΨ : MemLp Ψ 2 (μN n)) : Integrable (fun x => w x * (Φ x * Ψ x)) (μN n) := by
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  exact (int_mul_L2 hΦ hΨ).bdd_mul hw.aestronglyMeasurable hB

lemma QNH_expand (hw : Continuous w) (v : PotH) {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
    (hΨ : Ψ ∈ DomN τ n) (s : ℝ) :
    QNH τ w v (Φ + s • Ψ) = QNH τ w v Φ +
      2 * s * (kinN2 Φ Ψ + ∫ x, w x * (Φ x * Ψ x) ∂μN n + v (rhoE2 τ Φ Ψ)) +
      s ^ 2 * QNH τ w v Ψ := by
  have hW := integral_expand (integrable_w_mul hw hΦ.1 hΦ.1) (integrable_w_mul hw hΦ.1 hΨ.1)
    (integrable_w_mul hw hΨ.1 hΨ.1) s
  simp only [QNH, hW, kinN_expand (h1NW_of_mem hΦ) (h1NW_of_mem hΨ) s, rhoE_expand hΦ hΨ s,
    map_add, map_smul, smul_eq_mul]
  ring

lemma kinN_smul {Ψ : Cfg n → ℝ} (hΨ : H1NW Ψ) (c : ℝ) : kinN (c • Ψ) = c ^ 2 * kinN Ψ := by
  simp only [kinN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd : dWN k (c • Ψ) =ᵐ[μN n] fun x => c * dWN k Ψ x :=
    dWN_ae_eq ((dWN_spec (hΨ.2 k)).const_mul c)
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hd] with x hx
  rw [hx]; ring

lemma QNH_smul (v : PotH) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN τ n) (c : ℝ) :
    QNH τ w v (c • Ψ) = c ^ 2 * QNH τ w v Ψ := by
  have hW : ∫ x, w x * ((c • Ψ) x * (c • Ψ) x) ∂μN n =
      c ^ 2 * ∫ x, w x * (Ψ x * Ψ x) ∂μN n := by
    rw [← integral_const_mul]; congr 1; funext x
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [QNH, hW, kinN_smul (h1NW_of_mem hΨ), rhoE_smul hΨ, map_smul, smul_eq_mul]
  ring

/-- On null states the energy is nonnegative. -/
lemma QNH_null (v : PotH) {χ : Cfg n → ℝ} (hχ : χ ∈ DomN τ n) (h0 : ∫ x, χ x ^ 2 ∂μN n = 0) :
    0 ≤ QNH τ w v χ := by
  have hzz : (fun x => χ x * χ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (χ x)) (int_mul_L2 hχ.1 hχ.1)).1
      (by rw [← h0]; simp only [sq])
  have hw0 : ∫ x, w x * (χ x * χ x) ∂μN n = 0 := by
    rw [integral_congr_ae (hzz.mono fun x hx => by simp only [hx, Pi.zero_apply, mul_zero] :
      (fun x => w x * (χ x * χ x)) =ᵐ[μN n] fun _ => (0 : ℝ))]
    simp
  rw [QNH, rhoE_null hχ h0, map_zero, hw0]
  linarith [kinN_nonneg χ]

/-- A normalised ground state with energy `E` has `E ∫ χ² ≤ QNH χ` on Neumann states. -/
lemma EN_mul_leH {v : PotH} {Φ : Cfg n → ℝ} (h : IsGSNH τ w v Φ)
    {χ : Cfg n → ℝ} (hχ : χ ∈ DomN τ n) : QNH τ w v Φ * ∫ x, χ x ^ 2 ∂μN n ≤ QNH τ w v χ := by
  set m := ∫ x, χ x ^ 2 ∂μN n
  have hm : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact QNH_null v hχ h0.symm
  · set c := 1 / √m
    have hc2 : c ^ 2 = 1 / m := by rw [div_pow, Real.sq_sqrt hm, one_pow]
    have hn : ∫ x, (c • χ) x ^ 2 ∂μN n = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, integral_const_mul, hc2]
      exact one_div_mul_cancel hpos.ne'
    have := h.2.2 _ (Submodule.smul_mem _ c hχ) hn
    rw [QNH_smul v hχ, hc2] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos] at this
    linarith [mul_comm (QNH τ w v Φ) m]

/-- **The Euler–Lagrange equation** for a normalised `N`-particle Neumann ground state of an
`H⁻¹` potential, with energy `E = QNH Φ`. -/
theorem euler_lagrangeNH (hw : Continuous w) {v : PotH} {Φ : Cfg n → ℝ} (h : IsGSNH τ w v Φ)
    {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN τ n) :
    kinN2 Φ Ψ + ∫ x, w x * (Φ x * Ψ x) ∂μN n + v (rhoE2 τ Φ Ψ) =
      QNH τ w v Φ * ∫ x, Φ x * Ψ x ∂μN n := by
  have hΦ := h.1
  have hsq : ∀ s : ℝ, ∫ x, (Φ + s • Ψ) x ^ 2 ∂μN n =
      1 + 2 * s * ∫ x, Φ x * Ψ x ∂μN n + s ^ 2 * ∫ x, Ψ x ^ 2 ∂μN n := fun s => by
    have := integral_expand (μ := μN n) (g := fun _ => (1 : ℝ)) (ψ := Φ) (φ := Ψ)
      (by simpa using int_mul_L2 hΦ.1 hΦ.1) (by simpa using int_mul_L2 hΦ.1 hΨ.1)
      (by simpa using int_mul_L2 hΨ.1 hΨ.1) s
    simp only [one_mul] at this
    simp only [sq]; rw [this, ← h.2.1]; simp only [sq]
  have key := eq_zero_of_quad (a := kinN2 Φ Ψ + ∫ x, w x * (Φ x * Ψ x) ∂μN n +
      v (rhoE2 τ Φ Ψ) - QNH τ w v Φ * ∫ x, Φ x * Ψ x ∂μN n)
    (c := QNH τ w v Ψ - QNH τ w v Φ * ∫ x, Ψ x ^ 2 ∂μN n) fun s => by
    have h1 := EN_mul_leH h (add_mem hΦ (Submodule.smul_mem _ s hΨ))
    rw [hsq, QNH_expand hw v hΦ hΨ] at h1
    linarith
  linarith

/-! ### `|Φ|` for bosons -/

/-- For bosons, `ρ_{|Φ|} = ρ_Φ`. -/
lemma rhoE_abs {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN .bos n) :
    rhoE .bos (fun x => |Φ x|) = rhoE .bos Φ :=
  eq_of_int fun u => by
    rw [int_rhoE (abs_mem_DomN hΦ), int_rhoE hΦ]
    simp only [pfN, abs_mul_abs_self]

/-- **For bosons, `|Φ|` is a ground state whenever `Φ` is.** -/
theorem isGSNH_abs {v : PotH} {Φ : Cfg n → ℝ} (h : IsGSNH .bos w v Φ) :
    IsGSNH .bos w v (fun x => |Φ x|) := by
  have hD := abs_mem_DomN h.1
  have hn : ∫ x, |Φ x| ^ 2 ∂μN n = 1 := by simpa [sq_abs] using h.2.1
  have hQ : QNH .bos w v (fun x => |Φ x|) ≤ QNH .bos w v Φ := by
    simp only [QNH, rhoE_abs h.1, abs_mul_abs_self]
    linarith [kinN_abs_le h.1]
  exact ⟨hD, hn, fun Ψ hΨ hΨn => hQ.trans (h.2.2 Ψ hΨ hΨn)⟩

end DFT.Continuum.Line
