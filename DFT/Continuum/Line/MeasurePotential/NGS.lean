/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.NEnergy

/-!
# `N`-particle ground states in a measure potential

For every measure potential `ν ∈ C([0, 1])*`, continuous interaction `w`, and bosons or fermions,
`T + w + ν` has a normalised ground state in `H¹₀` (**`exists_isGSN`**).

Direct method. A minimising sequence `Φ_j` has bounded kinetic energy (`QMN_ge`). In sine
coefficients a subsequence converges coordinatewise, hence in `ℓ²` (`tendsto_l2`), to an admissible
`a`; `Φ = Σ a_m s_m` has kinetic energy `Σ λ a² ≤ lim inf T(Φ_j)`, and `Φ_j → Φ` in `L²`, so the
interaction energy converges. The continuous square roots `g_j = √ρ̂_j` are bounded in `H¹₀`, so a
further subsequence converges uniformly (`exists_weak_subseq`, `tendsto_primP`); the limit of `g_j²`
has the integrals of `ρ_Φ`, so it is `ρ̂_Φ` (`rhoHat_unique`), and `ν(ρ̂_j) → ν(ρ̂_Φ)`.

* `cN_sub`, `int_abs_sq_sub_le`, `tendsto_int_abs_sq_sub`, `tendsto_int_pot`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ}

/-! ### Auxiliary convergence lemmas -/

lemma cN_sub {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n))
    (m : Fin (n + 1) → ℕ) : cN m (f - g) = cN m f - cN m g := by
  have h1 := int_mul_L2 (memLp_cont (n := n) (continuous_smd m)) hf
  have h2 := int_mul_L2 (memLp_cont (n := n) (continuous_smd m)) hg
  rw [cN_eq, cN_eq, cN_eq, ← integral_sub h1 h2]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)

/-- `∫ |P² - Φ²| ≤ ε (∫ P² + ∫ Φ²) + ε⁻¹ ∫ (P - Φ)²`. -/
lemma int_abs_sq_sub_le {P Φ : Cfg n → ℝ} (hP : MemLp P 2 (μN n)) (hΦ : MemLp Φ 2 (μN n))
    {ε : ℝ} (hε : 0 < ε) :
    ∫ x, |P x ^ 2 - Φ x ^ 2| ∂μN n ≤
      ε * (∫ x, P x ^ 2 ∂μN n + ∫ x, Φ x ^ 2 ∂μN n) + ε⁻¹ * ∫ x, (P x - Φ x) ^ 2 ∂μN n := by
  have iP := int_sq hP
  have iΦ := int_sq hΦ
  have iD : Integrable (fun x => (P x - Φ x) ^ 2) (μN n) := int_sq (hP.sub hΦ)
  have hpt : ∀ x, |P x ^ 2 - Φ x ^ 2| ≤ ε * (P x ^ 2 + Φ x ^ 2) + ε⁻¹ * (P x - Φ x) ^ 2 :=
    fun x => by
      rw [abs_sq_sub_sq_le]
      have h1 : |P x + Φ x| ^ 2 ≤ 2 * (P x ^ 2 + Φ x ^ 2) := by
        rw [sq_abs]; nlinarith [sq_nonneg (P x - Φ x)]
      have h2 : |P x - Φ x| * |P x + Φ x| ≤
          ε / 2 * |P x + Φ x| ^ 2 + ε⁻¹ / 2 * |P x - Φ x| ^ 2 := by
        have := sq_nonneg (ε * |P x + Φ x| - |P x - Φ x|)
        have hε' : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
        nlinarith [inv_pos.2 hε]
      rw [sq_abs] at h2
      have h3 : ε / 2 * (P x + Φ x) ^ 2 ≤ ε * (P x ^ 2 + Φ x ^ 2) := by
        nlinarith [sq_nonneg (P x - Φ x)]
      have h4 : ε⁻¹ / 2 * |P x - Φ x| ^ 2 ≤ ε⁻¹ * (P x - Φ x) ^ 2 := by
        rw [sq_abs]; nlinarith [inv_pos.2 hε, sq_nonneg (P x - Φ x)]
      linarith
  have iPΦ : Integrable (fun x => P x ^ 2 + Φ x ^ 2) (μN n) := iP.add iΦ
  have i1 : Integrable (fun x => ε * (P x ^ 2 + Φ x ^ 2)) (μN n) := iPΦ.const_mul ε
  have i2 : Integrable (fun x => ε⁻¹ * (P x - Φ x) ^ 2) (μN n) := iD.const_mul _
  calc ∫ x, |P x ^ 2 - Φ x ^ 2| ∂μN n
      ≤ ∫ x, ε * (P x ^ 2 + Φ x ^ 2) + ε⁻¹ * (P x - Φ x) ^ 2 ∂μN n :=
        integral_mono (iP.sub iΦ).abs (i1.add i2) hpt
    _ = _ := by
        rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_add iP iΦ]

/-- `L²` convergence of normalised states gives `L¹` convergence of their squares. -/
lemma tendsto_int_abs_sq_sub {P : ℕ → Cfg n → ℝ} {Φ : Cfg n → ℝ} (hP : ∀ j, MemLp (P j) 2 (μN n))
    (hΦ : MemLp Φ 2 (μN n)) (hPn : ∀ j, ∫ x, P j x ^ 2 ∂μN n = 1) (hΦn : ∫ x, Φ x ^ 2 ∂μN n = 1)
    (hD : Tendsto (fun j => ∫ x, (P j x - Φ x) ^ 2 ∂μN n) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, |P j x ^ 2 - Φ x ^ 2| ∂μN n) atTop (𝓝 0) := by
  set D := fun j => ∫ x, (P j x - Φ x) ^ 2 ∂μN n
  have hD0 : ∀ j, 0 ≤ D j := fun j => integral_nonneg fun _ => sq_nonneg _
  set ε := fun j : ℕ => √(D j + 1 / ((j : ℝ) + 1))
  have hεpos : ∀ j, 0 < ε j := fun j => Real.sqrt_pos.2 (by have := hD0 j; positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h0 := (hD.add tendsto_one_div_add_atTop_nhds_zero_nat).sqrt
    rw [add_zero, Real.sqrt_zero] at h0
    exact h0
  refine squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_)
    (by simpa using hεlim.const_mul 3)
  have h1 := int_abs_sq_sub_le (hP j) hΦ (hεpos j)
  rw [hPn j, hΦn] at h1
  have h2 : (ε j)⁻¹ * D j ≤ ε j := by
    rw [inv_mul_le_iff₀ (hεpos j), ← sq, Real.sq_sqrt (by have := hD0 j; positivity)]
    have : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
    linarith
  linarith

/-- Uniform convergence in `C([0, 1])` gives convergence of `∫ v p`. -/
lemma tendsto_int_pot (v : C01) {p : ℕ → C01} {q : C01} (h : Tendsto p atTop (𝓝 q)) :
    Tendsto (fun j => ∫ t, iccExt v t * iccExt (p j) t ∂vol01) atTop (𝓝 (∫ t, iccExt v t * iccExt q t ∂vol01)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  have hb : ∀ (r : C01) (x : ℝ), |iccExt r x| ≤ ‖r‖ := fun r x => by
    simpa [SturmLiouville.iccExt] using r.norm_coe_le_norm _
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) (by simpa using h.const_mul ‖v‖)
  have i1 : Integrable (fun t => iccExt v t * iccExt (p j) t) vol01 :=
    Integrable.of_bound ((continuous_iccExt v).mul (continuous_iccExt _)).aestronglyMeasurable
      (‖v‖ * ‖p j‖) (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hb v t) (hb _ t) (abs_nonneg _)
          (norm_nonneg _))
  have i2 : Integrable (fun t => iccExt v t * iccExt q t) vol01 :=
    Integrable.of_bound ((continuous_iccExt v).mul (continuous_iccExt _)).aestronglyMeasurable
      (‖v‖ * ‖q‖) (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hb v t) (hb _ t) (abs_nonneg _)
          (norm_nonneg _))
  rw [← integral_sub i1 i2]
  have hle : ∀ t, ‖iccExt v t * iccExt (p j) t - iccExt v t * iccExt q t‖ ≤ ‖v‖ * ‖p j - q‖ := fun t => by
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    have : iccExt (p j) t - iccExt q t = iccExt (p j - q) t := rfl
    rw [this]
    exact mul_le_mul (hb v t) (hb _ t) (abs_nonneg _) (norm_nonneg _)
  calc ‖∫ t, iccExt v t * iccExt (p j) t - iccExt v t * iccExt q t ∂vol01‖ ≤ ‖v‖ * ‖p j - q‖ * vol01.real univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ hle)
    _ = ‖v‖ * ‖p j - q‖ := by simp

/-! ### Existence -/

variable {τ : Stat}

/-- **`N`-particle ground states exist for every measure potential**, every continuous interaction,
bosons or fermions. -/
theorem exists_isGSN (τ : Stat) {w : Cfg n → ℝ} (hw : Continuous w) (ν : PotM) :
    ∃ Φ : Cfg n → ℝ, IsGSN τ w ν Φ := by
  set S := {e | ∃ Φ ∈ DomW τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ QMN τ w ν Φ = e}
  obtain ⟨C, hC⟩ := QMN_ge (τ := τ) hw ν
  -- nonempty
  have hSne : S.Nonempty := by
    obtain ⟨a, ha⟩ := exists_adm (n := n) τ
    have hD := serW_mem (s := τ.toSym) ha.toDir
    have hn : ∫ x, serW a x ^ 2 ∂μN n = 1 := by
      rw [← (parsevalW (memLp_serW (a := a))).tsum_eq]
      simp only [cN_serW ha.sq]; exact ha.norm
    exact ⟨_, _, hD, hn, rfl⟩
  have hbdd : BddBelow S := ⟨-C, fun e ⟨Φ, hΦ, hn, he⟩ => by
    rw [← he]; have := hC Φ hΦ hn; linarith [kinW_nonneg Φ]⟩
  set E := sInf S
  have hE_le : ∀ Φ ∈ DomW τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 → E ≤ QMN τ w ν Φ :=
    fun Φ hΦ hn => csInf_le hbdd ⟨Φ, hΦ, hn, rfl⟩
  -- a minimising sequence
  have hseq : ∀ j : ℕ, ∃ Φ ∈ DomW τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧
      QMN τ w ν Φ < E + 1 / ((j : ℝ) + 1) := fun j => by
    obtain ⟨_, ⟨Φ, hΦ, hn, rfl⟩, h⟩ := exists_lt_of_csInf_lt hSne
      (lt_add_of_pos_right E (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)))
    exact ⟨Φ, hΦ, hn, h⟩
  choose Φ hΦ hΦn hΦE using hseq
  set M := 2 * (E + 1 + C)
  have hkin : ∀ j, kinW (Φ j) ≤ M := fun j => by
    have h1 := hC _ (hΦ j) (hΦn j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith [hΦE j]
  -- coefficients
  set c := fun j m => cN m (Φ j)
  have hc : ∀ j, Adm τ.toSym (c j) := fun j => adm_cNW (hΦ j) (hΦn j)
  have hckin : ∀ j, ∑' m, lam m * c j m ^ 2 ≤ M := fun j =>
    (Summable.tsum_le_of_sum_le (hc j).kin (sum_lam_le (h1W_of_mem (hΦ j)))).trans (hkin j)
  have hbox : ∀ j, c j ∈ Set.univ.pi fun _ : Fin (n + 1) → ℕ => Set.Icc (-1 : ℝ) 1 := fun j =>
    Set.mem_univ_pi.2 fun m => by
      have h : c j m ^ 2 ≤ 1 :=
        (hc j).norm ▸ (hc j).sq.le_tsum m (fun m' _ => sq_nonneg (c j m'))
      exact abs_le.1 ((sq_le_one_iff_abs_le_one _).1 h)
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : Fin (n + 1) → ℕ => isCompact_Icc).tendsto_subseq hbox
  rw [tendsto_pi_nhds] at hlim
  -- the limit coefficients
  have hak := lim_sum_le hlim (fun m => lam_nonneg m) (fun j => (hc (φ j)).kin)
    (fun j => hckin (φ j))
  have has := lim_sum_le hlim (w := fun _ => 1) (B := 1) (fun _ => zero_le_one)
    (fun j => by simpa using (hc (φ j)).sq) (fun j => by simpa using (hc (φ j)).norm.le)
  simp only [one_mul] at has
  have hsym : InS τ.toSym a := fun σ hσ m =>
    tendsto_nhds_unique (hlim (pmI σ m))
      (by simpa only [Function.comp_apply, (hc _).sym σ hσ m] using
        (hlim m).const_mul (τ.toSym.χ σ))
  have hnorm : ∑' m, a m ^ 2 = 1 := by
    refine le_antisymm has.2 (le_of_forall_pos_lt_add fun ε hε => ?_)
    obtain ⟨K, hK⟩ := exists_div_lt (M := M) hε
    have hT : 1 - M / ((K : ℝ) + 1) ≤ ∑ m ∈ box K, a m ^ 2 := by
      refine ge_of_tendsto' (tendsto_finsetSum (box (n := n) K) fun m _ => (hlim m).pow 2)
        fun j => ?_
      have := sum_box_ge (hc (φ j)).sq (hc (φ j)).kin (hckin (φ j)) K
      rwa [(hc (φ j)).norm] at this
    have := has.1.sum_le_tsum (box K) fun m _ => sq_nonneg (a m)
    linarith
  have ha : Adm τ.toSym a := ⟨⟨has.1, hak.1, hsym⟩, hnorm⟩
  set Ψ := serW a
  have hΨ : Ψ ∈ DomW τ n := serW_mem ha.toDir
  have hΨn : ∫ x, Ψ x ^ 2 ∂μN n = 1 := by
    rw [← (parsevalW (memLp_serW (a := a))).tsum_eq]
    simp only [cN_serW ha.sq]; exact ha.norm
  -- `L²` convergence along `φ`
  have hl2 := tendsto_l2 hlim (fun j => (hc (φ j)).sq) (fun j => (hc (φ j)).kin)
    (fun j => hckin (φ j)) has.1 hak.1 hak.2
  have hD : Tendsto (fun j => ∫ x, (Φ (φ j) x - Ψ x) ^ 2 ∂μN n) atTop (𝓝 0) := by
    refine hl2.congr fun j => ?_
    change _ = ∫ x, (Φ (φ j) - Ψ) x ^ 2 ∂μN n
    rw [← (parsevalW ((hΦ (φ j)).1.sub hΨ.1)).tsum_eq]
    refine tsum_congr fun m => ?_
    rw [cN_sub (hΦ (φ j)).1 hΨ.1, cN_serW ha.sq]; rfl
  have hL1 := tendsto_int_abs_sq_sub (fun j => (hΦ (φ j)).1) hΨ.1 (fun j => hΦn (φ j)) hΨn hD
  -- the continuous square roots of the densities, and a uniformly convergent subsequence
  set g := fun j => gN τ (Φ (φ j))
  have hg : ∀ j, H10 (g j) := fun j => h10_gN _
  set f := fun j => dL (hg j)
  have hfR : ∀ j, ‖f j‖ ≤ √M := fun j => by
    have h1 : ‖f j‖ ^ 2 ≤ M := by
      rw [norm_dL_sq]; exact (kinM_gN_le (hΦ (φ j))).trans (hkin _)
    have := Real.abs_le_sqrt h1
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  obtain ⟨F, ψ, hψ, hw'⟩ := exists_weak_subseq hfR
  have hP := tendsto_primP (f := fun k => f (ψ k)) (fun k => hfR _) hw'
  have hrho : ∀ k, rhoHat τ (Φ (φ (ψ k))) = primP (f (ψ k)) * primP (f (ψ k)) := fun k =>
    sqP_eq_primP _ fun t ht => prim_dL _ ht
  have hRlim : Tendsto (fun k => rhoHat τ (Φ (φ (ψ k)))) atTop
      (𝓝 (primP F * primP F)) := by
    simp only [hrho]; exact hP.mul hP
  -- the limit is the continuous density of `Ψ`
  have hid : rhoHat τ Ψ = primP F * primP F := by
    refine rhoHat_unique hΨ fun v => ?_
    have h1 := tendsto_int_pot v hRlim
    have h2 : Tendsto (fun k => ∫ t, iccExt v t * rhoN (Φ (φ (ψ k))) t ∂vol01) atTop
        (𝓝 (∫ t, iccExt v t * rhoN Ψ t ∂vol01)) := by
      have hL1' := hL1.comp hψ.tendsto_atTop
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ x, |iccExt v x| ≤ ‖v‖ := fun x => by simpa [SturmLiouville.iccExt] using v.norm_coe_le_norm _
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
        (by simpa using (hL1'.const_mul ((n + 1) * ‖v‖)))
      have hρi : ∀ (P : Cfg n → ℝ), MemLp P 2 (μN n) →
          Integrable (fun t => iccExt v t * rhoN P t) vol01 := fun P hP' =>
        ((integrable_marg hP').const_mul _).bdd_mul (continuous_iccExt v).aestronglyMeasurable
          (ae_of_all _ fun x => by simpa using hb x)
      rw [← integral_sub (hρi _ (hΦ _).1) (hρi _ hΨ.1)]
      calc ‖∫ t, iccExt v t * rhoN (Φ (φ (ψ k))) t - iccExt v t * rhoN Ψ t ∂vol01‖
          ≤ ∫ t, ‖v‖ * |rhoN (Φ (φ (ψ k))) t - rhoN Ψ t| ∂vol01 := by
            have hint : Integrable (fun t => ‖v‖ * |rhoN (Φ (φ (ψ k))) t - rhoN Ψ t|) vol01 := by
              have h1 : Integrable (rhoN (Φ (φ (ψ k)))) vol01 :=
                (integrable_marg (hΦ _).1).const_mul _
              have h2 : Integrable (rhoN Ψ) vol01 := (integrable_marg hΨ.1).const_mul _
              exact (h1.sub h2).abs.const_mul _
            refine norm_integral_le_of_norm_le hint (ae_of_all _ fun t => ?_)
            rw [← mul_sub, Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
        _ = ‖v‖ * ∫ t, |rhoN (Φ (φ (ψ k))) t - rhoN Ψ t| ∂vol01 := integral_const_mul _ _
        _ ≤ ‖v‖ * ((n + 1) * ∫ x, |Φ (φ (ψ k)) x ^ 2 - Ψ x ^ 2| ∂μN n) :=
            mul_le_mul_of_nonneg_left (integral_abs_rhoN_sub (hΦ _).1 hΨ.1) (norm_nonneg _)
        _ = (n + 1) * ‖v‖ * ∫ x, |Φ (φ (ψ k)) x ^ 2 - Ψ x ^ 2| ∂μN n := by ring
    have h1' : Tendsto (fun k => ∫ t, iccExt v t * rhoN (Φ (φ (ψ k))) t ∂vol01) atTop
        (𝓝 (∫ t, iccExt v t * iccExt (primP F * primP F) t ∂vol01)) :=
      h1.congr fun k => rhoHat_spec (hΦ _) v
    exact tendsto_nhds_unique h1' h2
  -- convergence of the interaction and potential terms
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  have hwlim : Tendsto (fun k => ∫ x, w x * (Φ (φ (ψ k)) x * Φ (φ (ψ k)) x) ∂μN n) atTop
      (𝓝 (∫ x, w x * (Ψ x * Ψ x) ∂μN n)) := by
    have hL1' := hL1.comp hψ.tendsto_atTop
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (by simpa using hL1'.const_mul B)
    have hi : ∀ (P : Cfg n → ℝ), MemLp P 2 (μN n) →
        Integrable (fun x => w x * (P x * P x)) (μN n) :=
      fun P hP' => (int_mul_L2 hP' hP').bdd_mul hw.aestronglyMeasurable hB
    rw [← integral_sub (hi _ (hΦ _).1) (hi _ hΨ.1)]
    refine (norm_integral_le_of_norm_le
      (((int_sq (hΦ (φ (ψ k))).1).sub (int_sq hΨ.1)).abs.const_mul B) ?_).trans
      (by rw [integral_const_mul]; exact le_rfl)
    filter_upwards [hB] with x hx
    rw [← mul_sub, norm_mul, Real.norm_eq_abs (Φ (φ (ψ k)) x * Φ (φ (ψ k)) x - Ψ x * Ψ x)]
    rw [show Φ (φ (ψ k)) x * Φ (φ (ψ k)) x - Ψ x * Ψ x = Φ (φ (ψ k)) x ^ 2 - Ψ x ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hνlim : Tendsto (fun k => ν (rhoHat τ (Φ (φ (ψ k))))) atTop (𝓝 (ν (rhoHat τ Ψ))) := by
    rw [hid]; exact (ν.continuous.tendsto _).comp hRlim
  -- the energies converge to `E`
  have hQlim : Tendsto (fun k => QMN τ w ν (Φ (φ (ψ k)))) atTop (𝓝 E) := by
    have hz : Tendsto (fun k : ℕ => E + 1 / ((φ (ψ k) : ℝ) + 1)) atTop (𝓝 E) := by
      have := (tendsto_const_nhds (x := E)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (hφ.comp hψ).tendsto_atTop)
      rw [add_zero] at this; exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun k => hE_le _ (hΦ _) (hΦn _)) fun k => (hΦE _).le
  set L := E - ∫ x, w x * (Ψ x * Ψ x) ∂μN n - ν (rhoHat τ Ψ)
  have hkinlim : Tendsto (fun k => kinW (Φ (φ (ψ k)))) atTop (𝓝 L) := by
    refine ((hQlim.sub hwlim).sub hνlim).congr fun k => ?_
    simp only [QMN, h0W_self]; ring
  -- lower semicontinuity of the kinetic energy
  have hle : ∀ T : Finset (Fin (n + 1) → ℕ), ∑ m ∈ T, lam m * a m ^ 2 ≤ L := fun T => by
    refine le_of_tendsto_of_tendsto
      (tendsto_finsetSum T fun m _ => (((hlim m).comp hψ.tendsto_atTop).pow 2).const_mul (lam m))
      hkinlim (Eventually.of_forall fun k => ?_)
    exact sum_lam_le (h1W_of_mem (hΦ _)) T
  have hkinΨ : kinW Ψ ≤ L := by
    rw [kinW_serW ha.toDir]
    exact Real.tsum_le_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg (a m))) hle
  refine ⟨Ψ, hΨ, hΨn, fun Φ' hΦ' hΦ'n => ?_⟩
  have : QMN τ w ν Ψ ≤ E := by simp only [QMN, h0W_self]; linarith
  exact this.trans (hE_le Φ' hΦ' hΦ'n)

end DFT.Continuum.Line
