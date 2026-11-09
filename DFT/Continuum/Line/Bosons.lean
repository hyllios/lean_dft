/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Nodal
import DFT.Continuum.Line.Hopf

/-!
# `N` interacting bosons on a line: the ground state has no zeros

For `n + 1` bosons on `[0, 1]` with a continuous interaction invariant under relabelling, the
ground state has no zeros in the open cube (the Perron–Frobenius property), so unique continuation
holds and Hohenberg–Kohn needs no further assumption.

* `no_pos_dk_bos`, `grad_zero_at_zero_bos`: a ground state has zero gradient at each of its zeros.
  The competitor is the smoothed modulus `h_ε(Φ)`, which is symmetric, and the test function is a
  symmetrised bump; this is the fermion argument of `Nodal` without the sign of the ordering.
* `gs_ne_zero_bos`: a ground state has no zeros in the open cube (Hopf's lemma on the cube).
* `ucp_bos`: unique continuation.
* `hk_interacting_bosons_line`: **Hohenberg–Kohn for `N` interacting bosons on a line**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box Metric

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

lemma sym_memB {f : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (hout : ∀ x, x ∉ Cube n → f x = 0) :
    sym f ∈ DomB n :=
  ⟨contDiff_sym hf, fun σ x => by rw [sym_pm, ch_bos, one_mul], fun x k hk =>
    Finset.sum_eq_zero fun σ _ => hout _ (pm_not_mem_cube hk σ)⟩

-- the main proof is long and keeps many constants in context
set_option maxHeartbeats 1000000 in
/-- A bosonic ground state cannot vanish at a point of the cube where `∂ₖΦ > 0`. -/
lemma no_pos_dk_bos {Φ : Cfg n → ℝ} (hΦ : IsGS (settingB n w hw) v Φ) {a : Cfg n}
    (ha : a ∈ Cube n) {k : Fin (n + 1)} (h0 : Φ a = 0) (hpos : 0 < dk k Φ a) : False := by
  have hD : Φ ∈ DomB n := hΦ.1
  have hsymΦ : ∀ σ x, Φ (pm σ x) = Φ x := fun σ x => by rw [hD.2.1 σ x, ch_bos, one_mul]
  set s0 := dk k Φ a with hs0
  obtain ⟨r, r', δ, hr, hr', hrr, hδ, hin, hsign⟩ :=
    box_data_line hD isOpen_univ ⟨ha, mem_univ a⟩ h0 hpos
  -- a symmetrised bump at `a`
  let β : ContDiffBump a := ⟨r, 2 * r, hr, by linarith⟩
  have hβout : ∀ x, x ∉ Cube n → β x = 0 := fun x hx => by
    by_contra h
    have : x ∈ tsupport β := subset_tsupport _ h
    rw [β.tsupport_eq] at this
    exact hx (hin x (mem_closedBall.mp this)).1.1
  set φs : Cfg n → ℝ := sym β with hφsd
  have hφsm : φs ∈ DomB n := sym_memB β.contDiff hβout
  have hφs0 : ∀ x, 0 ≤ φs x := fun x => Finset.sum_nonneg fun σ _ => β.nonneg' _
  -- the box
  set Bx := boxL a k r r' with hBx
  have hBxd : ∀ x ∈ Bx, dist x a ≤ r := fun x hx => dist_le_of_boxL hrr hr'.le hx
  have hφs1 : ∀ x ∈ Bx, 1 ≤ φs x := fun x hx => by
    have h1 : β (pm 1 x) = 1 := β.one_of_mem_closedBall (mem_closedBall.mpr (hBxd x hx))
    have : β (pm 1 x) ≤ φs x :=
      Finset.single_le_sum (f := fun σ => β (pm σ x)) (fun σ _ => β.nonneg' _)
        (Finset.mem_univ (1 : Equiv.Perm (Fin (n + 1))))
    linarith
  have hBxS : Bx ⊆ Cube n := fun x hx => (hin x (by linarith [hBxd x hx])).1.1
  have hBxd1 : ∀ x ∈ Bx, s0 / 2 < dk k Φ x := fun x hx => (hin x (by linarith [hBxd x hx])).2
  -- constants independent of `ε`
  set E := Q (settingB n w hw) v Φ / ip (μ := μN n) Φ Φ with hE
  set V : Cfg n → ℝ := fun x => w x + LN n v x - E with hV
  have hVc : Continuous V := (hw.add (continuous_LN v)).sub continuous_const
  have hφc : Continuous φs := hφsm.1.continuous
  have hΦc : Continuous Φ := hD.1.continuous
  set K1 := ∫ x, |V x| * |Φ x| ∂μN n with hK1d
  have hK1 : 0 ≤ K1 := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  set K2 := ∫ x, |V x| * φs x ∂μN n with hK2d
  have hK2 : 0 ≤ K2 := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (hφs0 x)
  set C := RfL .bos w hw v E φs φs with hCd
  have hC : 0 ≤ C := RfL_nonneg hΦ hφsm
  set L := s0 / 2 * (2 * r') ^ n with hLd
  have hL : 0 < L := by positivity
  set ε := min δ (min (L / (4 * (K2 + 1))) (L ^ 2 / (16 * (K1 * C + 1)))) with hεd
  have hε0 : 0 < ε := lt_min hδ (lt_min (by positivity) (by positivity))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ L / (4 * (K2 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ L ^ 2 / (16 * (K1 * C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  -- the competitor `h_ε(Φ)` and the Euler–Lagrange test `k_ε(Φ) φs`
  set H : Cfg n → ℝ := fun x => hε ε (Φ x) with hHd
  have hHm : H ∈ DomB n :=
    ⟨(contDiff_hε hε0).comp hD.1, fun σ x => by simp only [H, hsymΦ, ch_bos, one_mul],
      fun x l hl => by simp only [H, hD.2.2 x l hl, hε_zero hε0]⟩
  set g : Cfg n → ℝ := fun x => kε ε (Φ x) * φs x with hgd
  have hgm : g ∈ DomB n :=
    ⟨((contDiff_kε hε0).comp hD.1).mul hφsm.1, fun σ x => by
      simp only [g, hsymΦ, sym_pm, φs, ch_bos, one_mul],
      fun x l hl => by simp only [g, hφsm.2.2 x l hl, mul_zero]⟩
  have hφsd' : Differentiable ℝ φs := hφsm.1.differentiable (by norm_num)
  have dH : ∀ l x, dk l H x = 1 * (kε ε (Φ x) * dk l Φ x) := fun l x => by
    simp only [dk, H, one_mul]
    rw [fderiv_comp_applyL (hasDerivAt_hε hε0) (diffF hD)]
  have dg : ∀ l x, dk l g x = k2 ε (Φ x) * dk l Φ x * φs x + kε ε (Φ x) * dk l φs x :=
    fun l x => by
      simp only [dk, g]
      rw [fderiv_mul_applyL (f := fun y => kε ε (Φ y)) (g := φs)
        (((contDiff_kε hε0).comp hD.1).differentiable (by norm_num)) hφsd',
        fderiv_comp_applyL (hasDerivAt_kε hε0) (diffF hD)]
  have hk2c : Continuous (k2 ε) := continuous_k2 hε0
  have hkc : Continuous (kε ε) := (contDiff_kε hε0).continuous
  have hhc : Continuous (hε ε) := (contDiff_hε hε0).continuous
  have hgradc : Continuous fun x => ∑ l, dk l Φ x ^ 2 :=
    continuous_finsetSum _ fun l _ => (cont_dk hD l).pow 2
  set G : Cfg n → ℝ := fun x => k2 ε (Φ x) * (∑ l, dk l Φ x ^ 2) * φs x with hGd
  have hGc : Continuous G := ((hk2c.comp hΦc).mul hgradc).mul hφc
  -- lower bound: `∫ G ≥ L`
  have hlow : L ≤ ∫ x, G x ∂μN n := by
    have hcpt : IsCompact Bx := isCompact_boxL a k r r'
    have h1 : ∫ x in Bx, G x ≤ ∫ x, G x ∂μN n :=
      setIntegral_mono_set (integrableN hGc)
        (ae_of_all _ fun x => mul_nonneg (mul_nonneg (k2_pos hε0 _).le
          (Finset.sum_nonneg fun l _ => sq_nonneg _)) (hφs0 x)) hBxS.eventuallyLE
    have hFc : Continuous fun x => k2 ε (Φ x) * dk k Φ x := (hk2c.comp hΦc).mul (cont_dk hD k)
    have h2 : ∫ x in Bx, s0 / 2 * (k2 ε (Φ x) * dk k Φ x) ≤ ∫ x in Bx, G x := by
      refine setIntegral_mono_on ((continuous_const.mul hFc).continuousOn.integrableOn_compact
        hcpt) (hGc.continuousOn.integrableOn_compact hcpt) (measurableSet_boxL a k r r')
        fun x hx => ?_
      exact ar_lowN hpos (k2_pos hε0 (Φ x)) (hBxd1 x hx)
        (Finset.single_le_sum (f := fun l => dk l Φ x ^ 2) (fun l _ => sq_nonneg _)
          (Finset.mem_univ k)) (hφs1 x hx)
    have h3 := box_integral_line hD hε0 hr hr' hεδ hsign
    rw [integral_const_mul] at h2
    calc L = s0 / 2 * (2 * r') ^ n := rfl
      _ ≤ s0 / 2 * ∫ x in Bx, k2 ε (Φ x) * dk k Φ x :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ ≤ _ := h2
      _ ≤ _ := h1
  -- the cross term
  set X : Cfg n → ℝ := fun x => V x * (hε ε (Φ x) - Φ x * kε ε (Φ x)) * φs x with hXd
  have hXc : Continuous X := (hVc.mul ((hhc.comp hΦc).sub (hΦc.mul (hkc.comp hΦc)))).mul hφc
  set B := RfL .bos w hw v E H φs with hBd
  have hU : ∫ x, G x ∂μN n = ∫ x, X x ∂μN n - B := by
    have hEL := RfL_EL hΦ hgm
    rw [RfL_eq E hD hgm] at hEL
    rw [hBd, RfL_eq E hHm hφsm]
    have iA : Integrable (fun x => ∑ l, dk l Φ x * dk l g x +
        (w x + LN n v x - E) * (Φ x * g x)) (μN n) :=
      integrableN ((cont_kin hD hgm).add (hVc.mul (hΦc.mul hgm.1.continuous)))
    have iXG : Integrable (fun x => X x - G x) (μN n) := integrableN (hXc.sub hGc)
    have key : ∫ x, (∑ l, dk l H x * dk l φs x + (w x + LN n v x - E) * (H x * φs x)) ∂μN n =
        ∫ x, (∑ l, dk l Φ x * dk l g x + (w x + LN n v x - E) * (Φ x * g x)) ∂μN n +
          ∫ x, (X x - G x) ∂μN n := by
      rw [← integral_add iA iXG]
      congr 1; funext x
      have := ptwise_far (fun l => dk l H x) (fun l => dk l φs x) (fun l => dk l Φ x)
        (fun l => dk l φs x) (fun l => dk l g x) (S := 1) (S0 := 1) (hh := hε ε (Φ x))
        (V := w x + LN n v x - E) (Φv := Φ x) (φsv := φs x)
        (fun l => dH l x) (fun l => (one_mul _).symm) (fun l => dg l x) (one_mul 1)
      simp only [one_mul] at this
      simpa only [X, G, H, g] using this
    rw [key, hEL, zero_add, integral_sub (integrableN hXc) (integrableN hGc)]
    ring
  have hB1 : |∫ x, X x ∂μN n| ≤ ε * K2 := by
    calc |∫ x, X x ∂μN n| ≤ ∫ x, |X x| ∂μN n := abs_integral_le_integral_abs
      _ ≤ ∫ x, ε * (|V x| * φs x) ∂μN n := by
          refine integral_mono (integrableN hXc.abs)
            (integrableN (continuous_const.mul (hVc.abs.mul hφc))) fun x => ?_
          simp only [X, abs_mul, abs_of_nonneg (hφs0 x)]
          exact ar_X (abs_hε_sub hε0 (Φ x)) (hφs0 x)
      _ = ε * K2 := integral_const_mul _ _
  -- the energy of the competitor
  have hB2 : RfL .bos w hw v E H H ≤ 2 * ε * K1 := by
    have hself := RfL_self hΦ
    rw [RfL_eq E hD hD] at hself
    rw [RfL_eq E hHm hHm]
    have iΦ : Integrable (fun x => ∑ l, dk l Φ x * dk l Φ x +
        (w x + LN n v x - E) * (Φ x * Φ x)) (μN n) :=
      integrableN ((cont_kin hD hD).add (hVc.mul (hΦc.mul hΦc)))
    have ih : Integrable (fun x => ∑ l, dk l H x * dk l H x +
        (w x + LN n v x - E) * (H x * H x)) (μN n) :=
      integrableN ((cont_kin hHm hHm).add (hVc.mul (hHm.1.continuous.mul hHm.1.continuous)))
    have ihΦ : Integrable (fun x => (∑ l, dk l H x * dk l H x +
        (w x + LN n v x - E) * (H x * H x)) - (∑ l, dk l Φ x * dk l Φ x +
          (w x + LN n v x - E) * (Φ x * Φ x))) (μN n) := ih.sub iΦ
    have e : ∫ x, (∑ l, dk l H x * dk l H x + (w x + LN n v x - E) * (H x * H x)) ∂μN n =
        ∫ x, (∑ l, dk l Φ x * dk l Φ x + (w x + LN n v x - E) * (Φ x * Φ x)) ∂μN n +
          ∫ x, ((∑ l, dk l H x * dk l H x + (w x + LN n v x - E) * (H x * H x)) -
            (∑ l, dk l Φ x * dk l Φ x + (w x + LN n v x - E) * (Φ x * Φ x))) ∂μN n := by
      rw [← integral_add iΦ ihΦ]
      congr 1; funext x; ring
    rw [e, hself, zero_add]
    calc _ ≤ ∫ x, 2 * ε * (|V x| * |Φ x|) ∂μN n := by
          refine integral_mono ihΦ (integrableN (continuous_const.mul (hVc.abs.mul hΦc.abs)))
            fun x => ?_
          have hsq := abs_hε_sq_sub hε0 (Φ x)
          have hVle : (w x + LN n v x - E) * (hε ε (Φ x) ^ 2 - Φ x ^ 2) ≤
              |V x| * (2 * ε * |Φ x|) := by
            calc (w x + LN n v x - E) * (hε ε (Φ x) ^ 2 - Φ x ^ 2)
                ≤ |(w x + LN n v x - E) * (hε ε (Φ x) ^ 2 - Φ x ^ 2)| := le_abs_self _
              _ = |V x| * |hε ε (Φ x) ^ 2 - Φ x ^ 2| := by rw [abs_mul]
              _ ≤ |V x| * (2 * ε * |Φ x|) :=
                  mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
          have := energy_far (fun l => dk l H x) (fun l => dk l Φ x) (S := 1) (hh := hε ε (Φ x))
            (V := w x + LN n v x - E) (fun l => dH l x) (one_pow 2) (kε_sq_le hε0 (Φ x)) hVle
          simp only [one_mul] at this
          simpa only [H] using this
      _ = 2 * ε * K1 := integral_const_mul _ _
  have hB3 : B ^ 2 ≤ RfL .bos w hw v E H H * C := by
    refine discr_le hC fun t => ?_
    have h := RfL_nonneg hΦ ((DomB n).add_mem hHm ((DomB n).smul_mem t hφsm))
    rw [RfL_expand E hHm hφsm t] at h
    linarith
  have hA : L ≤ ε * K2 + |B| := by
    have h1 := hlow
    rw [hU] at h1
    have h2 := (abs_le.mp hB1).2
    have h3 := le_abs_self (∫ x, X x ∂μN n)
    linarith [neg_abs_le B]
  exact final_arith hL hK1 hK2 hC hε0 hε1 hε2 hA hB2 hB3

/-- **Critical zeros.** A ground state of `n + 1` interacting bosons has zero gradient at each of
its zeros in the open cube. -/
theorem grad_zero_at_zero_bos {Φ : Cfg n → ℝ} (hΦ : IsGS (settingB n w hw) v Φ) :
    ∀ x ∈ Cube n, Φ x = 0 → ∀ k, dk k Φ x = 0 := by
  intro x hx h0 k
  by_contra hd
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have e : dk k (-Φ) x = -dk k Φ x := by
      simp only [dk]; rw [fderiv_neg]; rfl
    exact no_pos_dk_bos (isGS_neg_line hΦ) hx (by simp [h0]) (by rw [e]; linarith)
  · exact no_pos_dk_bos hΦ hx h0 hpos

lemma convex_cube : Convex ℝ (Cube n) := convex_pi fun _ _ => convex_Ioo 0 1

/-- On the cube a bosonic ground state is positive everywhere or nonpositive everywhere. -/
lemma gs_pos_or_nonpos_bos (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (settingB n w hw) v Φ) :
    (∀ x ∈ Cube n, 0 < Φ x) ∨ ∀ x ∈ Cube n, Φ x ≤ 0 := by
  set E := Q (settingB n w hw) v Φ / ip (μ := μN n) Φ Φ
  set V : Cfg n → ℝ := fun x => w x + LN n v x - E
  have hV : Continuous V := (hw.add (continuous_LN v)).sub continuous_const
  have heq := strong_eq_line hws hΦ
  refine pos_or_nonpos_on isOpen_cube convex_cube.isPreconnected (c := fun x => max (V x) 0)
    hΦ.1.1 (hV.max continuous_const) (fun x => le_max_right _ _) (fun x hx hpos => ?_)
    (grad_zero_at_zero_bos hΦ)
  have e := heq x hx
  have h1 : 0 ≤ (max (V x) 0 - V x) * Φ x :=
    mul_nonneg (by linarith [le_max_left (V x) 0]) hpos.le
  simp only [V] at e h1 ⊢
  nlinarith

/-- **A bosonic ground state has no zeros in the open cube** (Perron–Frobenius). -/
theorem gs_ne_zero_bos (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (settingB n w hw) v Φ) : ∀ x ∈ Cube n, Φ x ≠ 0 := by
  intro x0 hx0 h0
  rcases gs_pos_or_nonpos_bos hws hΦ with h | h
  · exact (h x0 hx0).ne' h0
  rcases gs_pos_or_nonpos_bos hws (isGS_neg_line hΦ) with h' | h'
  · exact (h' x0 hx0).ne' (by simp [h0])
  have hz : ∀ x ∈ Cube n, Φ x = 0 := fun x hx =>
    le_antisymm (h x hx) (by have := h' x hx; simp only [Pi.neg_apply] at this; linarith)
  have hip : ip (μ := μN n) Φ Φ = 0 := by
    unfold ip
    refine integral_eq_zero_of_ae ?_
    refine (ae_restrict_iff' measurableSet_cube).2 (ae_of_all _ fun x hx => ?_)
    simp [hz x hx]
  exact absurd hΦ.2.1 (by rw [hip]; exact lt_irrefl 0)

/-- **Unique continuation for `N` bosons**: the ground state has no zeros in the cube. -/
theorem ucp_bos (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (settingB n w hw) v Φ) : ∀ᵐ x ∂μN n, Φ x ≠ 0 :=
  (ae_restrict_iff' measurableSet_cube).2 (ae_of_all _ fun x hx => gs_ne_zero_bos hws hΦ x hx)

/-- **Hohenberg–Kohn for `N` interacting bosons on a line.** For `n + 1` bosons on `[0, 1]` with
any continuous interaction invariant under relabelling, if ground states of continuous potentials
`v` and `v'` have the same one-body density, then `v - v'` is constant. -/
theorem hk_interacting_bosons_line (hws : ∀ σ x, w (pm σ x) = w x) {v' : Pot}
    {Φ Φ' : Cfg n → ℝ} (hΦ : IsGS (settingB n w hw) v Φ) (hΦ' : IsGS (settingB n w hw) v' Φ')
    (hρ : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
      ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) : ∃ k : ℝ, v - v' = k • one :=
  hk_line_of_ucp hΦ hΦ' hρ (ucp_bos hws hΦ)

end DFT.Continuum.Line
