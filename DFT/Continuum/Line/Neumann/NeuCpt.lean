/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuND

/-!
# Compactness, the ground-state energy, and the converse of Hellmann–Feynman

* **`compact_states`**: normalised Neumann states with bounded kinetic energy have a subsequence
  converging to a normalised state `Ψ`, with lower semicontinuous kinetic energy, convergent
  interaction energy, and `u(ρ_k) → u(ρ_Ψ)` for every `u ∈ H⁻¹`.
* `gsEH`: the ground-state energy `E(v)`; `gsEH_le`, `gsEH_of_isGSNH`, `isGSNH_of_le`.
* **`rhoE_eq_of_supergrad`**: if `ρ ∈ H¹` is a supergradient of `E` at `v`, that is
  `E(v') ≤ E(v) + (v' - v)(ρ)` for all `v'`, then `ρ` is the ground-state density of `v`. Along
  `v + t u`, `t → 0`, the ground states converge (up to a subsequence) to a ground state of `v`,
  which is unique, so `u(ρ_GS) ≤ u(ρ)` for every `u`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ}

/-- **Compactness of normalised states with bounded kinetic energy.** -/
theorem compact_states {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {Φ : ℕ → Cfg n → ℝ}
    (hΦ : ∀ j, Φ j ∈ DomN τ n) (hΦn : ∀ j, ∫ x, Φ j x ^ 2 ∂μN n = 1) {M : ℝ}
    (hkin : ∀ j, kinN (Φ j) ≤ M) :
    ∃ (Ψ : Cfg n → ℝ) (χ : ℕ → ℕ), StrictMono χ ∧ Ψ ∈ DomN τ n ∧ ∫ x, Ψ x ^ 2 ∂μN n = 1 ∧
      (∀ L : ℝ, (∀ ε > 0, ∀ᶠ k in atTop, kinN (Φ (χ k)) ≤ L + ε) → kinN Ψ ≤ L) ∧
      Tendsto (fun k => ∫ x, w x * (Φ (χ k) x * Φ (χ k) x) ∂μN n) atTop
        (𝓝 (∫ x, w x * (Ψ x * Ψ x) ∂μN n)) ∧
      ∀ u : PotH, Tendsto (fun k => u (rhoE τ (Φ (χ k)))) atTop (𝓝 (u (rhoE τ Ψ))) := by
  -- cosine coefficients
  set c := fun j m => cC m (Φ j)
  have hc : ∀ j, DirN τ.toSym (c j) := fun j => dirN_cC (hΦ j)
  have hcn : ∀ j, ∑' m, c j m ^ 2 = 1 := fun j =>
    (parsevalCW (hΦ j).1).tsum_eq.trans (hΦn j)
  have hckinC : ∀ j, ∑' m, lamC m * c j m ^ 2 ≤ M := fun j =>
    (tsum_lamC_le (hΦ j)).trans (hkin j)
  set K := 2 * M + 2 * π ^ 2 * (n + 1)
  have hclam : ∀ j, Summable (fun m => lam m * c j m ^ 2) ∧ ∑' m, lam m * c j m ^ 2 ≤ K :=
    fun j => by
      have hb : ∀ m, lam m * c j m ^ 2 ≤
          2 * (lamC m * c j m ^ 2) + 2 * π ^ 2 * (n + 1) * c j m ^ 2 := fun m => by
        have := lam_le_lamC m
        nlinarith [sq_nonneg (c j m)]
      have hs : Summable fun m => 2 * (lamC m * c j m ^ 2) + 2 * π ^ 2 * (n + 1) * c j m ^ 2 :=
        ((hc j).kin.mul_left 2).add ((hc j).sq.mul_left _)
      have hsl : Summable (fun m => lam m * c j m ^ 2) :=
        Summable.of_nonneg_of_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)) hb hs
      have e : ∑' m, (2 * (lamC m * c j m ^ 2) + 2 * π ^ 2 * (n + 1) * c j m ^ 2) =
          2 * ∑' m, lamC m * c j m ^ 2 + 2 * π ^ 2 * (n + 1) * ∑' m, c j m ^ 2 := by
        rw [Summable.tsum_add ((hc j).kin.mul_left 2) ((hc j).sq.mul_left _), tsum_mul_left,
          tsum_mul_left]
      refine ⟨hsl, (Summable.tsum_le_tsum hb hsl hs).trans ?_⟩
      rw [e, hcn j]; linarith [hckinC j]
  have hbox : ∀ j, c j ∈ Set.univ.pi fun _ : Fin (n + 1) → ℕ => Set.Icc (-1 : ℝ) 1 := fun j =>
    Set.mem_univ_pi.2 fun m => by
      have h : c j m ^ 2 ≤ 1 :=
        hcn j ▸ (hc j).sq.le_tsum m (fun m' _ => sq_nonneg (c j m'))
      exact abs_le.1 ((sq_le_one_iff_abs_le_one _).1 h)
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : Fin (n + 1) → ℕ => isCompact_Icc).tendsto_subseq hbox
  rw [tendsto_pi_nhds] at hlim
  -- the limit coefficients
  have hakC := lim_sum_le hlim (fun m => lamC_nonneg m) (fun j => (hc (φ j)).kin)
    (fun j => hckinC (φ j))
  have hak := lim_sum_le hlim (fun m => lam_nonneg m) (fun j => (hclam (φ j)).1)
    (fun j => (hclam (φ j)).2)
  have has := lim_sum_le hlim (w := fun _ => 1) (B := 1) (fun _ => zero_le_one)
    (fun j => by simpa using (hc (φ j)).sq) (fun j => by simpa using (hcn (φ j)).le)
  simp only [one_mul] at has
  have hsym : InS τ.toSym a := fun σ hσ m =>
    tendsto_nhds_unique (hlim (pmI σ m))
      (by simpa only [Function.comp_apply, (hc _).sym σ hσ m] using
        (hlim m).const_mul (τ.toSym.χ σ))
  have hnorm : ∑' m, a m ^ 2 = 1 := by
    refine le_antisymm has.2 (le_of_forall_pos_lt_add fun ε hε => ?_)
    obtain ⟨L, hL⟩ := exists_div_lt (M := K) hε
    have hT : 1 - K / ((L : ℝ) + 1) ≤ ∑ m ∈ box L, a m ^ 2 := by
      refine ge_of_tendsto' (tendsto_finsetSum (box (n := n) L) fun m _ => (hlim m).pow 2)
        fun j => ?_
      have := sum_box_ge (hc (φ j)).sq (hclam (φ j)).1 (hclam (φ j)).2 L
      rwa [hcn (φ j)] at this
    have := has.1.sum_le_tsum (box L) fun m _ => sq_nonneg (a m)
    linarith
  have ha : DirN τ.toSym a := ⟨has.1, hakC.1, hsym⟩
  set Ψ := serN a
  have hΨ : Ψ ∈ DomN τ n := serN_mem ha
  have hΨn : ∫ x, Ψ x ^ 2 ∂μN n = 1 := by
    rw [← (parsevalCW (memLp_serN (a := a))).tsum_eq]
    simp only [cC_serN ha.sq]; exact hnorm
  -- `L²` convergence along `φ`
  have hl2 := tendsto_l2 hlim (fun j => (hc (φ j)).sq) (fun j => (hclam (φ j)).1)
    (fun j => (hclam (φ j)).2) has.1 hak.1 hak.2
  have hD : Tendsto (fun j => ∫ x, (Φ (φ j) x - Ψ x) ^ 2 ∂μN n) atTop (𝓝 0) := by
    refine hl2.congr fun j => ?_
    change _ = ∫ x, (Φ (φ j) - Ψ) x ^ 2 ∂μN n
    rw [← (parsevalCW ((hΦ (φ j)).1.sub hΨ.1)).tsum_eq]
    refine tsum_congr fun m => ?_
    rw [cC_sub (hΦ (φ j)).1 hΨ.1, cC_serN ha.sq]; rfl
  have hL1 := tendsto_int_abs_sq_sub (fun j => (hΦ (φ j)).1) hΨ.1 (fun j => hΦn (φ j)) hΨn hD
  -- the `H¹` square roots of the densities: bounded in `H1E`
  set g := fun j => gNH τ (Φ (φ j))
  have hg : ∀ j, H1N (g j) := fun j => h1N_gNH _
  set e := fun j => toE (hg j)
  have hR : ∀ j, ‖(e j).snd‖ ≤ √M := fun j => by
    have h : ‖(e j).snd‖ ^ 2 ≤ M := by
      change ‖dN (hg j)‖ ^ 2 ≤ M
      rw [norm_dN_sq]; exact (kinM_gNH_le (hΦ _)).trans (hkin _)
    have := Real.abs_le_sqrt h
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  set K' := √(2 * (n + 1) + M)
  have hF : ∀ j, |(e j).fst| ≤ K' := fun j => by
    refine Real.abs_le_sqrt ?_
    have h1 := sq_le_H1N (hg j) one_pos (t := 0) ⟨le_rfl, zero_le_one⟩
    have h2 := integral_gNH_sq (τ := τ) (hΦ (φ j))
    rw [hΦn, mul_one] at h2
    have h3 := (kinM_gNH_le (hΦ (φ j))).trans (hkin (φ j))
    change g j 0 ^ 2 ≤ _
    have h2' : ∫ s, g j s ^ 2 ∂μ1 = n + 1 := h2
    have h3' : kinM (g j) ≤ M := h3
    rw [h2'] at h1
    linarith
  obtain ⟨c0, -, φ₁, hφ₁, hc0⟩ := tendsto_subseq_of_bounded (x := fun k => (e k).fst)
    (Metric.isBounded_Icc (-K') K') fun k => abs_le.1 (hF k)
  obtain ⟨G, φ₂, hφ₂, hwk⟩ := exists_weak_subseq (f := fun k => (e (φ₁ k)).snd) fun k => hR _
  set ψ := φ₁ ∘ φ₂
  have hψ : StrictMono ψ := hφ₁.comp hφ₂
  set e₀ : H1E := WithLp.toLp 2 (c0, G)
  have hfst : Tendsto (fun k => (e (ψ k)).fst) atTop (𝓝 e₀.fst) := hc0.comp hφ₂.tendsto_atTop
  have hP : Tendsto (fun k => evE (e (ψ k))) atTop (𝓝 (evE e₀)) := by
    simp only [evE_eq]
    exact ((ContinuousMap.continuous_const').tendsto _ |>.comp hfst).add
      (tendsto_primP (fun k => hR _) hwk)
  -- the limit is the density of `Ψ`
  have hRlim : Tendsto (fun k => evE (e (ψ k)) * evE (e (ψ k))) atTop
      (𝓝 (evE e₀ * evE e₀)) := hP.mul hP
  have hL1' := hL1.comp hψ.tendsto_atTop
  have hid : evE e₀ * evE e₀ =
      evE (toE (h1N_gNH (τ := τ) Ψ)) * evE (toE (h1N_gNH (τ := τ) Ψ)) := by
    refine pot_eq_of_integral fun u => ?_
    rw [integral_ext_evE_sq hΨ u]
    have h1 := (tendsto_int_pot u hRlim).congr fun k => integral_ext_evE_sq (hΦ (φ (ψ k))) u
    have h2 := tendsto_int_rhoN u (fun k => (hΦ (φ (ψ k))).1) hΨ.1 hL1'
    exact tendsto_nhds_unique h1 h2
  have hrho : dE e₀ = rhoE τ Ψ := by
    rw [dE_eq_sqE, rhoE]
    refine sqE_congr _ _ fun t ht => ?_
    have := congrArg (fun P : Pot => P ⟨t, ht⟩) hid
    simp only [ContinuousMap.mul_apply, evE_apply, fnE_toE _ ht] at this
    rw [sq, sq]; exact this
  refine ⟨Ψ, φ ∘ ψ, hφ.comp hψ, hΨ, hΨn, fun L hL => ?_, ?_, fun u => ?_⟩
  · have hle : ∀ T : Finset (Fin (n + 1) → ℕ), ∑ m ∈ T, lamC m * a m ^ 2 ≤ L := fun T => by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      refine le_of_tendsto (tendsto_finsetSum T fun m _ =>
        (((hlim m).comp hψ.tendsto_atTop).pow 2).const_mul (lamC m)) ?_
      filter_upwards [hL ε hε] with k hk
      exact (sum_lamC_le (h1NW_of_mem (hΦ _)) T).trans hk
    rw [kinN_serN ha]
    exact Real.tsum_le_of_sum_le (fun m => mul_nonneg (lamC_nonneg m) (sq_nonneg (a m))) hle
  · exact tendsto_int_w hw (fun k => (hΦ (φ (ψ k))).1) hΨ.1 hL1'
  · rw [← hrho]
    exact (tendsto_v_dE u hfst (fun k => hR _) hwk).congr fun k => by
      simp only [Function.comp_apply]; rw [rhoE, sqE_eq_dE]

/-! ### The ground-state energy -/

/-- The form-bound constant as a function of `‖v‖`. -/
noncomputable def cHr (R : ℝ) : ℝ := (R + 4 * R ^ 2) * (2 + 4 * (R + 4 * R ^ 2))

lemma cH_le_cHr {v : PotH} {R : ℝ} (h : ‖v‖ ≤ R) : cH v ≤ cHr R := by
  have h0 := norm_nonneg v
  unfold cH cHr
  have h1 : ‖v‖ + 4 * ‖v‖ ^ 2 ≤ R + 4 * R ^ 2 := by nlinarith
  have h2 : 0 ≤ ‖v‖ + 4 * ‖v‖ ^ 2 := by positivity
  exact mul_le_mul h1 (by linarith) (by positivity) (le_trans h2 h1)

variable (τ : Stat) (w : Cfg n → ℝ)

/-- **The ground-state energy** `E(v)`. -/
noncomputable def gsEH (v : PotH) : ℝ :=
  sInf {e | ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ QNH τ w v Φ = e}

variable {τ w}

lemma bddBelow_QNH (hw : Continuous w) (v : PotH) :
    BddBelow {e | ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ QNH τ w v Φ = e} := by
  obtain ⟨C, hC⟩ := QNH_ge (τ := τ) hw v
  exact ⟨-C, fun e ⟨Φ, hΦ, hn, he⟩ => by
    rw [← he]; have := hC Φ hΦ hn; linarith [kinN_nonneg Φ]⟩

lemma gsEH_le (hw : Continuous w) {v : PotH} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
    (hn : ∫ x, Φ x ^ 2 ∂μN n = 1) : gsEH τ w v ≤ QNH τ w v Φ :=
  csInf_le (bddBelow_QNH hw v) ⟨Φ, hΦ, hn, rfl⟩

lemma gsEH_of_isGSNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (h : IsGSNH τ w v Ψ) :
    gsEH τ w v = QNH τ w v Ψ :=
  le_antisymm (gsEH_le hw h.1 h.2.1)
    (le_csInf ⟨_, Ψ, h.1, h.2.1, rfl⟩ fun _ ⟨Φ, hΦ, hn, he⟩ => he ▸ h.2.2 Φ hΦ hn)

lemma isGSNH_of_le (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN τ n)
    (hn : ∫ x, Ψ x ^ 2 ∂μN n = 1) (h : QNH τ w v Ψ ≤ gsEH τ w v) : IsGSNH τ w v Ψ :=
  ⟨hΨ, hn, fun _ hΦ hΦn => h.trans (gsEH_le hw hΦ hΦn)⟩

lemma QNH_add_smul (v u : PotH) (t : ℝ) (Φ : Cfg n → ℝ) :
    QNH τ w (v + t • u) Φ = QNH τ w v Φ + t * u (rhoE τ Φ) := by
  simp only [QNH, add_apply, smul_apply, smul_eq_mul]
  ring

/-- A uniform kinetic bound for normalised states below a given energy. -/
lemma kinN_le_of_QNH {v : PotH} {R : ℝ} (hR : ‖v‖ ≤ R) {B : ℝ}
    (hB : ∀ᵐ x ∂μN n, ‖w x‖ ≤ B) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
    (hn : ∫ x, Φ x ^ 2 ∂μN n = 1) {E : ℝ} (hE : QNH τ w v Φ ≤ E) :
    kinN Φ ≤ 2 * (E + B + cHr R * (n + 1)) := by
  have h1 := abs_v_rhoE_le v hΦ
  rw [hn, mul_one] at h1
  have h2 := abs_int_w_le hB hΦ.1 hn
  have h3 : cH v * (n + 1) ≤ cHr R * (n + 1) :=
    mul_le_mul_of_nonneg_right (cH_le_cHr hR) (by positivity)
  rw [QNH] at hE
  linarith [neg_abs_le (v (rhoE τ Φ)), neg_abs_le (∫ x, w x * (Φ x * Φ x) ∂μN n)]

/-! ### The converse of Hellmann–Feynman -/

/-- **Every supergradient of `E` at `v` is the ground-state density of `v`.** -/
theorem rhoE_eq_of_supergrad (hw : Continuous w) {v : PotH} {ρ : H1E}
    (hsup : ∀ v' : PotH, gsEH τ w v' ≤ gsEH τ w v + (v' - v) ρ) {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) : rhoE τ Ψ = ρ := by
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  have key : ∀ u : PotH, u (rhoE τ Ψ) ≤ u ρ := by
    intro u
    set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have ht : ∀ k, 0 < t k := fun k => by positivity
    have ht1 : ∀ k, t k ≤ 1 := fun k => by
      simp only [t]; rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    choose Φ hΦ using fun k => exists_isGSNH τ hw (v + t k • u)
    have hEk : ∀ k, gsEH τ w (v + t k • u) = QNH τ w v (Φ k) + t k * u (rhoE τ (Φ k)) :=
      fun k => by rw [gsEH_of_isGSNH hw (hΦ k), QNH_add_smul]
    have hsupk : ∀ k, gsEH τ w (v + t k • u) ≤ gsEH τ w v + t k * u ρ := fun k => by
      have := hsup (v + t k • u)
      simpa only [add_sub_cancel_left, smul_apply, smul_eq_mul] using this
    have h1 : ∀ k, u (rhoE τ (Φ k)) ≤ u ρ := fun k => by
      have h2 := gsEH_le (v := v) hw (hΦ k).1 (hΦ k).2.1
      have := (hEk k).symm.le.trans (hsupk k)
      have h3 : t k * u (rhoE τ (Φ k)) ≤ t k * u ρ := by linarith
      exact le_of_mul_le_mul_left h3 (ht k)
    -- a uniform kinetic bound
    set E := QNH τ w v Ψ
    have hEv : gsEH τ w v = E := gsEH_of_isGSNH hw hΨ
    have hQk : ∀ k, QNH τ w (v + t k • u) (Φ k) ≤ E + |u (rhoE τ Ψ)| := fun k => by
      have h2 := (hΦ k).2.2 Ψ hΨ.1 hΨ.2.1
      rw [QNH_add_smul v u (t k) Ψ] at h2
      have : t k * u (rhoE τ Ψ) ≤ |u (rhoE τ Ψ)| := by
        calc t k * u (rhoE τ Ψ) ≤ t k * |u (rhoE τ Ψ)| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (ht k).le
          _ ≤ 1 * |u (rhoE τ Ψ)| := mul_le_mul_of_nonneg_right (ht1 k) (abs_nonneg _)
          _ = |u (rhoE τ Ψ)| := one_mul _
      linarith
    have hnorm : ∀ k, ‖v + t k • u‖ ≤ ‖v‖ + ‖u‖ := fun k => by
      calc ‖v + t k • u‖ ≤ ‖v‖ + ‖t k • u‖ := norm_add_le _ _
        _ = ‖v‖ + t k * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg (ht k).le]
        _ ≤ ‖v‖ + ‖u‖ := by
            have := mul_le_mul_of_nonneg_right (ht1 k) (norm_nonneg u); linarith
    have hkin : ∀ k, kinN (Φ k) ≤ 2 * (E + |u (rhoE τ Ψ)| + B + cHr (‖v‖ + ‖u‖) * (n + 1)) :=
      fun k => kinN_le_of_QNH (hnorm k) hB (hΦ k).1 (hΦ k).2.1 (hQk k)
    obtain ⟨Ψ', χ, hχ, hΨ'D, hΨ'n, hlsc, hW, hU⟩ :=
      compact_states hw (fun k => (hΦ k).1) (fun k => (hΦ k).2.1) hkin
    -- the limit is a ground state of `v`
    set L := gsEH τ w v - ∫ x, w x * (Ψ' x * Ψ' x) ∂μN n - v (rhoE τ Ψ')
    have htχ : Tendsto (fun k => t (χ k)) atTop (𝓝 0) := ht0.comp hχ.tendsto_atTop
    have hRlim : Tendsto (fun k => gsEH τ w v + t (χ k) * u ρ -
        ∫ x, w x * (Φ (χ k) x * Φ (χ k) x) ∂μN n - v (rhoE τ (Φ (χ k))) -
        t (χ k) * u (rhoE τ (Φ (χ k)))) atTop (𝓝 L) := by
      have := ((((tendsto_const_nhds (x := gsEH τ w v)).add (htχ.mul_const (u ρ))).sub hW).sub
        (hU v)).sub (htχ.mul (hU u))
      simpa [L] using this
    have hL : ∀ ε > 0, ∀ᶠ k in atTop, kinN (Φ (χ k)) ≤ L + ε := fun ε hε => by
      filter_upwards [hRlim.eventually_lt_const (lt_add_of_pos_right L hε)] with k hk
      have h2 := (hEk (χ k)).symm.le.trans (hsupk (χ k))
      rw [QNH] at h2
      linarith
    have hkΨ' := hlsc L hL
    have hGS : IsGSNH τ w v Ψ' := isGSNH_of_le hw hΨ'D hΨ'n (by rw [QNH]; linarith)
    have hρ' := rhoE_gsNH_unique hw hΨ hGS
    have hlim := hU u
    rw [hρ'] at hlim
    exact le_of_tendsto' hlim fun k => h1 (χ k)
  set d := rhoE τ Ψ - ρ
  set u : PotH := InnerProductSpace.toDual ℝ H1E d
  have h1 := key u
  have h2 := key (-u)
  simp only [neg_apply, neg_le_neg_iff] at h2
  have h3 : u d = 0 := by
    simp only [d, map_sub]; linarith
  have h4 : inner ℝ d d = 0 := by rw [← InnerProductSpace.toDual_apply_apply]; exact h3
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h4)

end DFT.Continuum.Line
