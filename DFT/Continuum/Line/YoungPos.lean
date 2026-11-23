/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.YoungSign
import DFT.Continuum.Line.WeakHK
import DFT.Continuum.Line.Unique

/-!
# Ground states of mixed symmetry: positivity and nondegeneracy

For `Σ_k v(x_k) + w` smooth on the closed cube and `w` invariant under relabelling, let `Φ` be a
ground state among states antisymmetric within the first `a` and within the last `N - a`
particles.

* `tl_ae_gs`: the competitor `Φ̃ = S · |Φ|` has the same norm and at most the same energy (its
  weak derivatives are bounded by those of `Φ`), so its sine coefficients minimise the
  coefficient-space energy and `Φ̃` is a.e. a `C²` ground state.
* `gs_sign_RY`: **`Φ` has a strict sign on the region `RY` where each group is ordered.** On `RY`
  the `C²` ground state equal to `Φ̃` a.e. is `|Φ| ≥ 0`, so its zeros are critical and Hopf's
  lemma applies; if it vanished on `RY`, `Φ` would vanish on the whole cube.
* `gs_unique_Y`: **the ground state of mixed symmetry is nondegenerate.**
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {a : ℕ}

/-! ### Bessel for weak derivatives -/

lemma bessel_wd {Φ G : Cfg n → ℝ} {k : Fin (n + 1)} (hW : IsWD k Φ G)
    (s : Finset (Fin (n + 1) → ℕ)) :
    ∑ m ∈ s, (π * (m k + 1) * cN m Φ) ^ 2 ≤ ∫ x, G x * G x ∂μN n := by
  set v : (Fin (n + 1) → ℕ) → HN n := fun m => (memLp_cont (contDiff_cmd k m).continuous).toLp
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro m m'
    simp only [v]
    rw [inner_toLp_left, ← cmd_orthonormal k m m']
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_cont (contDiff_cmd k m').continuous)] with x hx
    rw [hx]
  set G' : HN n := hW.1.toLp G
  have hinner : ∀ m, inner ℝ (v m) G' = π * (m k + 1) * cN m Φ := fun m => by
    simp only [v, G']
    rw [inner_toLp_left]
    have e : ∫ x, cmd k m x * (hW.1.toLp G : Cfg n → ℝ) x ∂μN n = ∫ x, G x * cmd k m x ∂μN n :=
      integral_congr_ae (by filter_upwards [MemLp.coeFn_toLp hW.1] with x hx; rw [hx, mul_comm])
    rw [e, ← neg_neg (∫ x, G x * cmd k m x ∂μN n), ← hW.2 _ (contDiff_cmd k m)]
    simp only [dk_cmd]
    rw [cN_eq, ← integral_neg, ← integral_const_mul]
    congr 1; funext x; ring
  have h := hv.sum_inner_products_le (x := G') (s := s)
  simp only [hinner, Real.norm_eq_abs, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [norm_sq_toLp]; congr 1; funext x; ring

lemma sum_lam_le_wd {Φ : Cfg n → ℝ} {G : Fin (n + 1) → Cfg n → ℝ} (hW : ∀ k, IsWD k Φ (G k))
    (s : Finset (Fin (n + 1) → ℕ)) :
    ∑ m ∈ s, lam m * cN m Φ ^ 2 ≤ ∑ k, ∫ x, G k x * G k x ∂μN n := by
  have e : ∑ m ∈ s, lam m * cN m Φ ^ 2 = ∑ k, ∑ m ∈ s, (π * (m k + 1) * cN m Φ) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [lam, ksq]; push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e]
  exact Finset.sum_le_sum fun k _ => bessel_wd (hW k) s

/-! ### The energy of a state of a symmetry type -/

lemma QS_eq {s : SymT n} {w : Cfg n → ℝ} {hw : Continuous w} (v : Pot) {Φ : Cfg n → ℝ}
    (hΦ : Φ ∈ DomS s) :
    Q (settingS s w hw) v Φ =
      ∫ x, ∑ k, dk k Φ x * dk k Φ x ∂μN n + ∫ x, (LN n v x + w x) * (Φ x * Φ x) ∂μN n := by
  have hc := hΦ.1.continuous
  change h0N n w Φ Φ + ∫ x, LN n v x * (Φ x * Φ x) ∂μN n = _
  rw [show (fun x => (LN n v x + w x) * (Φ x * Φ x)) =
      fun x => LN n v x * (Φ x * Φ x) + w x * (Φ x * Φ x) from funext fun x => by ring,
    integral_add (f := fun x => LN n v x * (Φ x * Φ x)) (g := fun x => w x * (Φ x * Φ x))
      (integrableN ((continuous_LN v).mul (hc.mul hc))) (integrableN (hw.mul (hc.mul hc)))]
  simp only [h0N]; ring

/-! ### The competitor is a ground state -/

section gs

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **The competitor `S · |Φ|` is a.e. a `C²` ground state.** -/
theorem tl_ae_gs {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ)
    (h1 : ip (μ := μN n) Φ Φ = 1) :
    ∃ Φ', IsGS (settingS (ymix a) w hw) v Φ' ∧ tl a Φ =ᵐ[μN n] Φ' := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hVc : Continuous V := (continuous_LN v).add hw
  have hVs : ∀ σ x, V (pm σ x) = V x := fun σ x => by simp only [V, LN_pm, hws]
  have hD : Φ ∈ DomY a n := hΦ.1
  obtain ⟨b, hb0, hbS, hK, hG⟩ := kernel_of_smooth hVc hF hVF
  -- the minimal energy is attained by a `C²` state
  obtain ⟨a0, ha0, hmin0⟩ := (kBd_of_kernel hb0 hbS hK).exists_min (V := V) (exists_adm_ymix (n := n) a)
  obtain ⟨hΦ0, hc0⟩ := ser_min2S hb0 hbS hK hVs ha0 hmin0 (by norm_num) (by norm_num) hG
  have hip0 : ip (μ := μN n) (ser a0) (ser a0) = 1 := by
    rw [ip_eq_tsum hΦ0.1.continuous]; simp only [hc0]; exact ha0.norm
  have hQ0 : Q (settingS (ymix a) w hw) v (ser a0) = E0 V (ymix a) := by
    rw [Q_eq_Fn_S hw v hΦ0, funext hc0, hmin0]
  have hQΦ : Q (settingS (ymix a) w hw) v Φ ≤ E0 V (ymix a) := by
    have := hΦ.2.2 (ser a0) hΦ0
    rwa [hip0, h1, mul_one, mul_one, hQ0] at this
  -- the coefficients of `Φ̃`
  have htc := continuous_tl hD
  have hmem : MemLp (tl a Φ) 2 (μN n) := memLp_cont htc
  set c : (Fin (n + 1) → ℕ) → ℝ := fun m => cN m (tl a Φ)
  have hsym : InS (ymix (n := n) a) c := fun σ hσ m => by
    change cN (pmI σ m) (tl a Φ) = sgn σ * cN m (tl a Φ)
    rw [cN_eq, cN_eq, ← integral_pm σ, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_injective] with x hx
    simp only [smd_pm]
    rw [tl_pm hD hσ hx]; ring
  have hkin : ∀ s : Finset (Fin (n + 1) → ℕ), ∑ m ∈ s, lam m * c m ^ 2 ≤
      ∑ k, ∫ x, Gt a Φ k x * Gt a Φ k x ∂μN n :=
    sum_lam_le_wd fun k => isWD_tl hD k
  have hT : ∑ k, ∫ x, Gt a Φ k x * Gt a Φ k x ∂μN n ≤ ∫ x, ∑ k, dk k Φ x * dk k Φ x ∂μN n := by
    rw [integral_finsetSum (f := fun k x => dk k Φ x * dk k Φ x) _ fun k _ =>
      integrableN ((contDiff_dk hD.1 k).continuous.mul (contDiff_dk hD.1 k).continuous)]
    refine Finset.sum_le_sum fun k _ => integral_mono (int_mul_L2 (memLp_Gt hD k) (memLp_Gt hD k))
      (integrableN ((contDiff_dk hD.1 k).continuous.mul (contDiff_dk hD.1 k).continuous))
      fun x => ?_
    have h := abs_Gt_le hD k x
    rw [← abs_mul_abs_self (Gt a Φ k x), ← abs_mul_abs_self (dk k Φ x)]
    exact mul_self_le_mul_self (abs_nonneg _) h
  have hsq : ∀ x, tl a Φ x * tl a Φ x = Φ x * Φ x := fun x => by
    rw [← sq, ← sq, tl_sq hD]
  have hnorm : ∫ x, tl a Φ x ^ 2 ∂μN n = 1 := by
    rw [← h1]; simp only [ip, sq, hsq]
  have ha : Adm (ymix (n := n) a) c :=
    { sq := (parsevalW hmem).summable
      kin := summable_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)) hkin
      sym := hsym
      norm := (parsevalW hmem).tsum_eq.trans hnorm }
  have hFn : Fn V c ≤ Q (settingS (ymix a) w hw) v Φ := by
    rw [Fn, Bf_cNW (V := V) hVc hmem, QS_eq v hD]
    have hpot : ∫ x, V x * (tl a Φ x * tl a Φ x) ∂μN n = ∫ x, V x * (Φ x * Φ x) ∂μN n := by
      simp only [hsq]
    rw [hpot]
    gcongr
    exact (Summable.tsum_le_of_sum_le (summable_of_sum_le
      (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)) hkin) hkin).trans hT
  have hE0 : E0 V (ymix a) ≤ Fn V c := csInf_le ((kBd_of_kernel hb0 hbS hK).bddBelow_Fn (ymix a)) ⟨c, ha, rfl⟩
  have hmin : Fn V c = E0 V (ymix a) := le_antisymm (hFn.trans hQΦ) hE0
  obtain ⟨hΦ1, hc1⟩ := ser_min2S hb0 hbS hK hVs ha hmin (by norm_num) (by norm_num) hG
  have hip' : ip (μ := μN n) (ser c) (ser c) = 1 := by
    rw [ip_eq_tsum hΦ1.1.continuous]; simp only [hc1]; exact ha.norm
  refine ⟨ser c, ⟨hΦ1, by rw [hip']; exact one_pos, fun φ hφ => ?_⟩, ?_⟩
  · rw [Q_eq_Fn_S hw v hΦ1, funext hc1, hmin, hip', mul_one, Q_eq_Fn_S hw v hφ,
      ip_eq_tsum hφ.1.continuous]
    exact (kBd_of_kernel hb0 hbS hK).Fn_ge (Dir_cN_S hφ)
  · exact ae_eq_of_cN_eq hmem (memLp_cont hΦ1.1.continuous) fun m => (hc1 m).symm

omit hws hF hVF in
/-- A state of mixed symmetry vanishing on `RY` vanishes on the cube. -/
lemma eq_zero_of_RY {Φ : Cfg n → ℝ} (hD : Φ ∈ DomY a n) (h : ∀ x ∈ RY a n, Φ x = 0) :
    ∀ x ∈ Cube n, Φ x = 0 := by
  intro x hx
  by_cases hc : ∃ i j, i ≠ j ∧ SameB a i j ∧ x i = x j
  · obtain ⟨i, j, hij, hs, he⟩ := hc
    exact eq_zero_of_collisionY hD hij hs he
  · push Not at hc
    obtain ⟨σ, hσ, hR⟩ := exists_YG_mem_RY (a := a) hx hc
    have h0 := h _ hR
    rw [show Φ (pm σ x) = sgn σ * Φ x from hD.2.1 σ hσ x] at h0
    rcases sgn_eq_or σ with hs | hs <;> rw [hs] at h0 <;> linarith

/-- **A ground state of mixed symmetry has a strict sign on the ordered region.** -/
theorem gs_sign_RY {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) :
    (∀ x ∈ RY a n, 0 < Φ x) ∨ ∀ x ∈ RY a n, Φ x < 0 := by
  -- normalise
  have hs := hΦ.2.1
  set c := (√(ip (μ := μN n) Φ Φ))⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hs).ne'
  have hcc : c * c * ip (μ := μN n) Φ Φ = 1 := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hs.le, inv_mul_cancel₀ hs.ne']
  have hΦ1 := isGS_smul hΦ hc
  have hip1 : ip (μ := μN n) (c • Φ) (c • Φ) = 1 := by rw [ip_smul_self, hcc]
  have hD1 : c • Φ ∈ DomY a n := hΦ1.1
  obtain ⟨Φ', hΦ', hae⟩ := tl_ae_gs hws hF hVF hΦ1 hip1
  -- on `RY`, `Φ' = |cΦ|`
  have hRC : RY a n ⊆ Cube n := fun x hx => hx.1
  have heq : EqOn (tl a (c • Φ)) Φ' (RY a n) := by
    have h' : tl a (c • Φ) =ᵐ[volume.restrict (RY a n)] Φ' :=
      ae_restrict_of_ae_restrict_of_subset hRC hae
    exact Measure.eqOn_open_of_ae_eq h' isOpen_RY (continuous_tl hD1).continuousOn
      hΦ'.1.1.continuous.continuousOn
  have habs : ∀ x ∈ RY a n, Φ' x = |c * Φ x| := fun x hx => by
    rw [← heq hx, tl_RY hx]; rfl
  have hnn : ∀ x ∈ RY a n, 0 ≤ Φ' x := fun x hx => by rw [habs x hx]; exact abs_nonneg _
  -- Hopf on `RY`
  set E := Q (settingS (ymix a) w hw) v Φ' / ip (μ := μN n) Φ' Φ'
  set V : Cfg n → ℝ := fun x => w x + LN n v x - E
  have hV : Continuous V := (hw.add (continuous_LN v)).sub continuous_const
  have heqn := strong_eq_Y hws hΦ'
  have hpn := pos_or_nonpos_on isOpen_RY (convex_RY (a := a)).isPreconnected
    (c := fun x => max (V x) 0) hΦ'.1.1 (hV.max continuous_const) (fun x => le_max_right _ _)
    (fun x hx hpos => by
      have e := heqn x hx.1
      have h1 : 0 ≤ (max (V x) 0 - V x) * Φ' x :=
        mul_nonneg (by linarith [le_max_left (V x) 0]) hpos.le
      simp only [V] at e h1 ⊢
      nlinarith)
    (fun x hx h0 k => by
      have hmin : IsLocalMin Φ' x := by
        filter_upwards [isOpen_RY.mem_nhds hx] with y hy
        rw [h0]; exact hnn y hy
      simp [dk, hmin.fderiv_eq_zero])
  have hne : ∀ x ∈ RY a n, Φ x ≠ 0 := by
    rcases hpn with hp | hp
    · intro x hx h0
      have := hp x hx
      rw [habs x hx, h0, mul_zero, abs_zero] at this
      exact lt_irrefl 0 this
    · -- `Φ' = 0` on `RY`, so `cΦ = 0` on the cube
      have hz : ∀ x ∈ RY a n, (c • Φ) x = 0 := fun x hx => by
        have h0 : Φ' x = 0 := le_antisymm (hp x hx) (hnn x hx)
        rw [habs x hx] at h0
        simpa using h0
      have hzC := eq_zero_of_RY hD1 hz
      have : ip (μ := μN n) (c • Φ) (c • Φ) = 0 := by
        unfold ip
        refine integral_eq_zero_of_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
        simp [hzC x hx]
      rw [hip1] at this; exact absurd this one_ne_zero
  -- a continuous function without zeros on a preconnected set has a strict sign
  by_contra hno
  push Not at hno
  obtain ⟨⟨p, hp, hp0⟩, ⟨q, hq, hq0⟩⟩ := hno
  have hp0' : Φ p < 0 := lt_of_le_of_ne hp0 (hne p hp)
  have hq0' : 0 < Φ q := lt_of_le_of_ne hq0 (hne q hq).symm
  obtain ⟨z, hz, hz0⟩ := (convex_RY (a := a)).isPreconnected.intermediate_value hp hq
    hΦ.1.1.continuous.continuousOn ⟨hp0'.le, hq0'.le⟩
  exact hne z hz hz0

omit hws hF hVF in
/-- The point `x_i = (i + 1) / (n + 2)` lies in `RY`. -/
lemma x0_mem_RY : (fun i : Fin (n + 1) => ((i : ℕ) + 1 : ℝ) / (n + 2)) ∈ RY a n := by
  obtain ⟨x, hx, -⟩ := exists_inj_cube (n := n)
  refine ⟨fun i _ => ?_, fun i j hij _ => ?_⟩
  · have hi : (i : ℕ) < n + 1 := i.2
    have hi' : ((i : ℕ) : ℝ) + 1 < n + 2 := by
      have : ((i : ℕ) : ℝ) < n + 1 := by exact_mod_cast hi
      linarith
    exact ⟨by positivity, by rw [div_lt_one (by positivity)]; exact hi'⟩
  · have hn : (0 : ℝ) < n + 2 := by positivity
    rw [div_lt_div_iff_of_pos_right hn]
    have : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    linarith

/-- **The ground state of mixed symmetry is nondegenerate.** -/
theorem gs_unique_Y {Φ Ψ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ)
    (hΨ : IsGS (settingS (ymix a) w hw) v Ψ) : ∃ c : ℝ, ∀ x ∈ CubeC n, Φ x = c * Ψ x := by
  set x0 : Cfg n := fun i => ((i : ℕ) + 1 : ℝ) / (n + 2)
  have hx0 : x0 ∈ RY a n := x0_mem_RY
  have hne : ∀ {Θ : Cfg n → ℝ}, IsGS (settingS (ymix a) w hw) v Θ → Θ x0 ≠ 0 := fun hΘ => by
    rcases gs_sign_RY hws hF hVF hΘ with h | h
    · exact (h x0 hx0).ne'
    · exact (h x0 hx0).ne
  have hΨ0 := hne hΨ
  set s := -(Φ x0 / Ψ x0)
  have hχ0 : (Φ + s • Ψ) x0 = 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]; field_simp; ring
  have hD : Φ + s • Ψ ∈ DomY a n := (DomY a n).add_mem hΦ.1 ((DomY a n).smul_mem s hΨ.1)
  have hip : ip (μ := μN n) (Φ + s • Ψ) (Φ + s • Ψ) = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) (integral_nonneg fun x => mul_self_nonneg _)
    exact hne (isGS_add_smul hΦ hΨ s hpos) hχ0
  have hc := hD.1.continuous
  have hae : (fun x => (Φ + s • Ψ) x * (Φ + s • Ψ) x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) (integrableN (hc.mul hc))).1 hip
  have hz : EqOn (fun x => (Φ + s • Ψ) x * (Φ + s • Ψ) x) (fun _ => 0) (Cube n) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_cube (hc.mul hc).continuousOn continuousOn_const
  refine ⟨-s, fun x hx => ?_⟩
  by_cases hxo : x ∈ Cube n
  · have := mul_self_eq_zero.1 (hz hxo)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  · have : ∃ k, x k = 0 ∨ x k = 1 := by
      by_contra hne'
      push Not at hne'
      exact hxo fun k _ => ⟨lt_of_le_of_ne (hx k (mem_univ k)).1 (hne' k).1.symm,
        lt_of_le_of_ne (hx k (mem_univ k)).2 (hne' k).2⟩
    obtain ⟨k, hk⟩ := this
    rw [hΦ.1.2.2 x k hk, hΨ.1.2.2 x k hk, mul_zero]

end gs

end DFT.Continuum.Line
