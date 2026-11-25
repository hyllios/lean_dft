/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasureNPos
import DFT.Continuum.Line.UcpY

/-!
# Unique continuation for fermionic ground states of measure potentials

For `N` fermions with a measure potential `ν` and a continuous interaction `w`, every `H¹₀` ground
state is nonzero almost everywhere (**`gsN_ne_zero_fer`**), and its density is positive on `(0, 1)`
(**`rhoHat_pos_fer`**). With `Line/MeasureNPos`: **`vrepMeasN_pos`**, ground-state densities of
measure potentials are positive on `(0, 1)` for both statistics.

As for continuous potentials (`Line/UcpY`, with all particles in one Young group, `a = N`): the
chamber state `Φ = Σ_σ sgn σ · (1_R |Ψ|) ∘ σ` is again a ground state (`isGSN_PhiY`), and its
bosonic companion `B = Σ_σ (1_R |Ψ|) ∘ σ = |Ψ|` satisfies the weak equation against symmetric test
functions vanishing on the diagonals (`eq_PhiBY_meas`). The potential term is `ν(p)` for a
continuous `p` with the integrals of `B φ`; for Moser's test function `0 ≤ B φ ≤ sup η²`, which
bounds `‖p‖` (`norm_pot_le_of_int`), and Moser's estimate holds on balls in the chamber
(`logData_ballY_meas`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Metric

variable {n : ℕ} {w : Cfg n → ℝ}

/-- The fermionic states as Young states. -/
lemma mem_fer_iff {Φ : Cfg n → ℝ} : Φ ∈ DomW .fer n ↔ Φ ∈ DomWS (ymix (n := n) (n + 1)) := by
  rw [DomW_fer_eq]

/-- **The chamber state of a fermionic ground state is a ground state.** -/
theorem isGSN_PhiY (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ} (hΨ : IsGSN .fer w ν Ψ) :
    IsGSN .fer w ν (PhiY (n + 1) Ψ) := by
  have hY := mem_fer_iff.1 hΨ.1
  have hD : PhiY (n + 1) Ψ ∈ DomW .fer n := mem_fer_iff.2 (PhiY_mem hY)
  have hsq : ∀ᵐ x ∂μN n, PhiY (n + 1) Ψ x * PhiY (n + 1) Ψ x = Ψ x * Ψ x := by
    filter_upwards [abs_PhiY hY] with x hx
    rw [← abs_mul_abs_self, hx, abs_mul_abs_self]
  have hn : ∫ x, PhiY (n + 1) Ψ x ^ 2 ∂μN n = 1 := by
    rw [← hΨ.2.1]; exact integral_congr_ae (by filter_upwards [hsq] with x hx; rw [sq, sq, hx])
  have hρ : rhoHat .fer (PhiY (n + 1) Ψ) = rhoHat .fer Ψ := pot_eq_of_integral fun v => by
    rw [int_rhoHat (w := w) hw hD, int_rhoHat (w := w) hw hΨ.1]
    exact integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])
  have hQ : QMN .fer w ν (PhiY (n + 1) Ψ) ≤ QMN .fer w ν Ψ := by
    simp only [QMN, h0W_self, hρ]
    have e : ∫ x, w x * (PhiY (n + 1) Ψ x * PhiY (n + 1) Ψ x) ∂μN n =
        ∫ x, w x * (Ψ x * Ψ x) ∂μN n :=
      integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])
    rw [e]; linarith [kinW_PhiY_le hY]
  exact ⟨hD, hn, fun Φ hΦ hΦn => hQ.trans (hΨ.2.2 Φ hΦ hΦn)⟩

/-- **The companion satisfies the weak equation** against symmetric test functions vanishing
linearly on the diagonals, with a continuous `p` having the integrals of `B φ`. -/
theorem eq_PhiBY_meas (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ} (hΨ : IsGSN .fer w ν Ψ)
    {φ : Cfg n → ℝ} (hφ : H1W φ) (hφs : ∀ σ, YG (n + 1) σ → ∀ x, φ (pm σ x) = φ x)
    (hL : ∀ p ∈ pY (n + 1) n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1|) :
    ∃ p : Pot, (∀ v : Pot, ∫ t, ext v t * ext p t ∂μ1 =
        ∫ x, LN n v x * (PhiBY (n + 1) Ψ x * φ x) ∂μN n) ∧
      h0W n w (PhiBY (n + 1) Ψ) φ + ν p =
        QMN .fer w ν (PhiY (n + 1) Ψ) * ∫ x, PhiBY (n + 1) Ψ x * φ x ∂μN n := by
  have hY := mem_fer_iff.1 hΨ.1
  have hG := isGSN_PhiY hw hΨ
  have hφD : phiY (n + 1) φ ∈ DomW .fer n := mem_fer_iff.2 (phiY_mem hφ hL)
  have hel := euler_lagrangeN hw hG hφD
  have hp : ∀ᵐ x ∂μN n, PhiY (n + 1) Ψ x * phiY (n + 1) φ x = PhiBY (n + 1) Ψ x * φ x := by
    filter_upwards [ae_cube, ae_injective] with x hx hinj
    rw [(PhiY_sgnY (Ψ := Ψ) hx hinj 0).1, phiY_sgnY hφs hx hinj]
    linear_combination (PhiBY (n + 1) Ψ x * φ x) * sgnY_mul_self hx hinj
  have hd : ∀ k, ∀ᵐ x ∂μN n, dW k (PhiY (n + 1) Ψ) x * dW k (phiY (n + 1) φ) x =
      dW k (PhiBY (n + 1) Ψ) x * dW k φ x := fun k => by
    filter_upwards [ae_cube, ae_injective, dW_ae_eq (sum_PhiY hY k).2,
      dW_ae_eq (sum_PhiBY hY k).2, dW_phiY_ae hφ hφs hL k] with x hx hinj h1 h2 h3
    rw [h1, h2, h3, (PhiY_sgnY (Ψ := Ψ) hx hinj k).2]
    linear_combination (DPhiBY (n + 1) Ψ k x * dW k φ x) * sgnY_mul_self hx hinj
  have e1 : ∫ x, PhiY (n + 1) Ψ x * phiY (n + 1) φ x ∂μN n =
      ∫ x, PhiBY (n + 1) Ψ x * φ x ∂μN n := integral_congr_ae hp
  have e3 : h0W n w (PhiY (n + 1) Ψ) (phiY (n + 1) φ) = h0W n w (PhiBY (n + 1) Ψ) φ := by
    simp only [h0W]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => integral_congr_ae (hd k)
    · exact integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  refine ⟨rhoHat2 .fer (PhiY (n + 1) Ψ) (phiY (n + 1) φ), fun v => ?_, ?_⟩
  · rw [int_rhoHat2 (w := w) hw hG.1 hφD]
    exact integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx]; rfl)
  · rw [e1, e3] at hel; exact hel

/-- A fermionic ground state of a measure potential gives the logarithmic data on closed balls in
the chamber. -/
theorem logData_ballY_meas (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSN .fer w ν Ψ) {x0 : Cfg n} {R : ℝ} (hR : 0 ≤ R)
    (hsub : closedBall x0 R ⊆ RY (n + 1) n) : LogData (PhiBY (n + 1) Ψ) (closedBall x0 R) := by
  have hY := mem_fer_iff.1 hΨ.1
  set E := QMN .fer w ν (PhiY (n + 1) Ψ)
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  set K := |E| + max B 0 + ‖ν‖ * (n + 1)
  have hK0 : 0 ≤ K := by positivity
  set η := etaY (n := n) (n + 1)
  have hη : ContDiff ℝ 1 η := contDiff_etaY
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_closedBall x0 R).exists_isMinOn
    ⟨x0, mem_closedBall_self hR⟩ (continuous_abs.comp hη.continuous).continuousOn
  set u := PhiBY (n + 1) Ψ
  have hu0 : ∀ x, 0 ≤ u x := PhiBY_nonneg Ψ
  -- `η² ≤ M` for a bound `M` of `η`
  obtain ⟨Mη, hMη⟩ : ∃ M, ∀ x ∈ Cube n, |η x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ => isCompact_Icc :
      IsCompact (CubeC n)).exists_bound_of_continuousOn hη.continuous.continuousOn
    exact ⟨M, fun x hx => by simpa using hM x fun j _ => Ioo_subset_Icc_self (hx j trivial)⟩
  set M2 := max Mη 0 ^ 2
  refine ⟨h1W_PhiBY hY, ae_of_all _ hu0, isClosed_closedBall.measurableSet,
    fun x hx => (hsub hx).1, convex_closedBall x0 R, η, hη.continuous,
    |η xm|, abs_pos.2 (etaY_ne_zero (hsub hxm)), fun x hx => hmin hx,
    4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * (K * max M2 1), ?_, fun ε hε => ?_⟩
  · have : 0 ≤ ∑ k, ∫ x, dk k η x ^ 2 ∂μN n :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    have : 0 ≤ max M2 1 := le_max_of_le_right zero_le_one
    positivity
  refine log_estimate_core (h1W_PhiBY hY) (ae_of_all _ hu0) hη etaY_wall hε ?_
  set φ := logTest η u ε
  have hφs : ∀ σ, YG (n + 1) σ → ∀ x, φ (pm σ x) = φ x := fun σ hσ x => by
    simp only [φ, logTest, η, etaY_pm hσ, u, PhiBY_pm Ψ hσ]
  have hφη : ∀ᵐ x ∂μN n, |φ x| ≤ max Bη 0 / ε * |η x| := by
    filter_upwards [hBη] with x hx
    rw [Real.norm_eq_abs] at hx
    have hp : 0 < u x + ε := by linarith [hu0 x]
    have e : φ x = η x * η x / (u x + ε) := by
      simp only [φ, logTest, Gr_of_nonneg (hu0 x)]; field_simp; ring
    rw [e, abs_div, abs_of_pos hp, abs_mul, div_le_iff₀ hp]
    have h1 : |η x| ≤ max Bη 0 := hx.trans (le_max_left _ _)
    have h2 : max Bη 0 / ε * |η x| * ε ≤ max Bη 0 / ε * |η x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith [hu0 x])
        (mul_nonneg (div_nonneg (le_max_right _ _) hε.le) (abs_nonneg _))
    have h3 : max Bη 0 / ε * |η x| * ε = max Bη 0 * |η x| := by field_simp
    nlinarith [abs_nonneg (η x)]
  have hL : ∀ p ∈ pY (n + 1) n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1| := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    obtain ⟨Lp, hLp0, hLp⟩ := abs_le_of_plane' hη hp'.1.ne
      fun x hx => etaY_diag x _ _ hp'.1.ne hp'.2 hx
    refine ⟨max Bη 0 / ε * Lp, mul_nonneg (div_nonneg (le_max_right _ _) hε.le) hLp0, ?_⟩
    filter_upwards [hφη, hLp] with x h1 h2
    calc |φ x| ≤ max Bη 0 / ε * |η x| := h1
      _ ≤ max Bη 0 / ε * (Lp * |x p.2 - x p.1|) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (le_max_right _ _) hε.le)
      _ = _ := by ring
  have hφH := h1W_logTest (h1W_PhiBY hY) hη etaY_wall hε
  obtain ⟨p, hpint, hel⟩ := eq_PhiBY_meas hw hΨ hφH hφs hL
  rw [h0W] at hel
  -- `0 ≤ u φ ≤ η² ≤ M2`
  have hb : ∀ᵐ x ∂μN n, 0 ≤ u x * φ x ∧ u x * φ x ≤ max M2 1 := by
    filter_upwards [ae_cube] with x hxc
    have hp : 0 < u x + ε := by linarith [hu0 x]
    have hφx : φ x = η x * η x / (u x + ε) := by
      simp only [φ, logTest, Gr_of_nonneg (hu0 x)]
      field_simp; ring
    constructor
    · rw [hφx]; exact mul_nonneg (hu0 x) (div_nonneg (mul_self_nonneg _) hp.le)
    · have h1 : u x * φ x ≤ η x * η x := by
        rw [hφx, mul_div_assoc', div_le_iff₀ hp]
        nlinarith [mul_self_nonneg (η x), hu0 x]
      have h2 : η x * η x ≤ M2 := by
        have := hMη x hxc
        have h' : |η x| ≤ max Mη 0 := this.trans (le_max_left _ _)
        rw [← abs_mul_abs_self]
        simp only [M2, sq]
        exact mul_le_mul h' h' (abs_nonneg _) ((abs_nonneg _).trans h')
      exact h1.trans (h2.trans (le_max_left _ _))
  have hM1 : 0 ≤ max M2 1 := le_max_of_le_right zero_le_one
  have iuφ := int_mul_L2 (h1W_PhiBY hY).1 hφH.1
  have hI : 0 ≤ ∫ x, u x * φ x ∂μN n ∧ ∫ x, u x * φ x ∂μN n ≤ max M2 1 := by
    refine ⟨integral_nonneg_of_ae (hb.mono fun x hx => hx.1), ?_⟩
    calc ∫ x, u x * φ x ∂μN n ≤ ∫ _x, max M2 1 ∂μN n :=
          integral_mono_ae iuφ (integrable_const _) (hb.mono fun x hx => hx.2)
      _ = max M2 1 := by
          simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]
  have hW : |∫ x, w x * (u x * φ x) ∂μN n| ≤ max B 0 * max M2 1 := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, w x * (u x * φ x) ∂μN n‖ ≤ ∫ x, max B 0 * (u x * φ x) ∂μN n := by
          refine norm_integral_le_of_norm_le (iuφ.const_mul _) ?_
          filter_upwards [hB, hb] with x hx hx'
          rw [norm_mul, Real.norm_eq_abs (u x * φ x), abs_of_nonneg hx'.1]
          exact mul_le_mul_of_nonneg_right (hx.trans (le_max_left _ _)) hx'.1
      _ = max B 0 * ∫ x, u x * φ x ∂μN n := integral_const_mul _ _
      _ ≤ max B 0 * max M2 1 := mul_le_mul_of_nonneg_left hI.2 (le_max_right _ _)
  have hN := norm_pot_le_of_int iuφ hM1 (hb.mono fun x hx => hx.1) (hb.mono fun x hx => hx.2)
    hpint
  have hν : |ν p| ≤ ‖ν‖ * (n + 1) * max M2 1 := by
    have := ν.le_opNorm p
    rw [Real.norm_eq_abs] at this
    calc |ν p| ≤ ‖ν‖ * ‖p‖ := this
      _ ≤ ‖ν‖ * ((n + 1) * max M2 1) := mul_le_mul_of_nonneg_left hN (norm_nonneg ν)
      _ = _ := by ring
  have hE : |E * ∫ x, u x * φ x ∂μN n| ≤ |E| * max M2 1 := by
    rw [abs_mul, abs_of_nonneg hI.1]
    exact mul_le_mul_of_nonneg_left hI.2 (abs_nonneg _)
  have hKe : K * max M2 1 = |E| * max M2 1 + max B 0 * max M2 1 + ‖ν‖ * (n + 1) * max M2 1 := by
    simp only [K]; ring
  rw [hKe]
  linarith [neg_abs_le (E * ∫ x, u x * φ x ∂μN n), le_abs_self (∫ x, w x * (u x * φ x) ∂μN n),
    le_abs_self (ν p)]

/-- **Fermionic ground states of measure potentials are nonzero almost everywhere.** -/
theorem gsN_ne_zero_fer (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSN .fer w ν Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  have hY := mem_fer_iff.1 hΨ.1
  set u := PhiBY (n + 1) Ψ
  have hum := (h1W_PhiBY hY).1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  have hloc : ∀ x0 ∈ RY (n + 1) n, ∃ B, IsOpen B ∧ x0 ∈ B ∧ B ⊆ RY (n + 1) n ∧
      ((∀ᵐ y ∂volume.restrict B, y ∈ Z) ∨ (∀ᵐ y ∂volume.restrict B, y ∉ Z)) := by
    intro x0 hx0
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_RY x0 hx0
    set R := δ / 4
    have hR : 0 < R := by positivity
    have hR2 : 2 * R < δ := by simp only [R]; linarith
    have hP : closedBall x0 (2 * R) ⊆ RY (n + 1) n := (closedBall_subset_ball hR2).trans hball
    have hL := logData_ballY_meas hw hΨ (by positivity) hP
    set P := closedBall x0 (2 * R)
    have hPc : P ⊆ Cube n := fun x hx => (hP hx).1
    have hinv : ∀ k (h : ℝ), 0 ≤ h →
        ∀ᵐ x ∂volume, x ∈ SP P h k → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
      intro k h hh
      have hv' := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae hv
      filter_upwards [hL.zero_set_translate k hh, hv, hv'] with x hx h1 h2 hxS
      simp only [Z, mem_ofPred_eq]
      rw [← h1 (hPc hxS.1), ← h2 (hPc hxS.2)]
      exact hx hxS
    have hPpi : P = univ.pi fun j => closedBall (x0 j) (2 * R) := closedBall_pi x0 (by positivity)
    have hV : ∀ t : Cfg n, ∀ᵐ x ∂volume, x ∈ P → x + t ∈ P → (x ∈ Z ↔ x + t ∈ Z) := by
      intro t
      have hA := invariant_all_gen hinv
      rw [hPpi] at hA ⊢
      exact invariant_vec_gen hA t
    refine ⟨ball x0 R, isOpen_ball, mem_ball_self hR,
      (ball_subset_ball (by linarith)).trans hball, ?_⟩
    refine const_on_set hZ hPc isOpen_ball (convex_ball x0 R).isPreconnected hR ?_ hV
    intro x hx t ht
    rw [hPpi]
    rw [ball_pi x0 hR] at hx
    refine Set.mem_univ_pi.2 fun j => ?_
    have h1 := Set.mem_univ_pi.1 hx j
    have h2 := Set.mem_univ_pi.1 ht j
    rw [mem_ball, Real.dist_eq] at h1
    rw [mem_closedBall, Real.dist_eq, Pi.sub_apply]
    have h3 : |t j| ≤ R := abs_le.2 h2
    calc |x j - t j - x0 j| ≤ |x j - x0 j| + |t j| := by
          rw [show x j - t j - x0 j = (x j - x0 j) + -t j by ring]
          exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ 2 * R := by linarith
  have hUc : ∀ᵐ x ∂volume.restrict (RY (n + 1) n), u x = u' x :=
    (ae_restrict_iff' measurableSet_RY).2 (by filter_upwards [hv] with x hx hxU using hx hxU.1)
  have hsym : ∀ (q : ℝ → Prop) σ, YG (n + 1) σ → ∀ x, q (u (pm σ x)) ↔ q (u x) :=
    fun q σ hσ x => by simp only [u, PhiBY_pm Ψ hσ]
  rcases null_or_conull_of_local convex_RY.isPreconnected hloc with h | h
  · exfalso
    have h0 : ∀ᵐ x ∂μN n, u x = 0 := ae_of_ae_RY (hsym (· = 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx])
    have hz : ∀ᵐ x ∂μN n, Ψ x ^ 2 = 0 := by
      filter_upwards [h0, PhiBY_ae_eq_abs hY] with x h1 h2
      have : |Ψ x| = 0 := h2 ▸ h1
      rw [abs_eq_zero.1 this]; ring
    have := integral_eq_zero_of_ae hz
    rw [hΨ.2.1] at this; exact one_ne_zero this
  · have h0 : ∀ᵐ x ∂μN n, u x ≠ 0 := ae_of_ae_RY (hsym (· ≠ 0)) (by
      filter_upwards [h, hUc] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rwa [he])
    filter_upwards [h0, PhiBY_ae_eq_abs hY] with x h1 h2
    have : |Ψ x| ≠ 0 := h2 ▸ h1
    exact abs_ne_zero.1 this

/-- **The density of a fermionic ground state of a measure potential is positive on `(0, 1)`.** -/
theorem rhoHat_pos_fer (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ} (hΨ : IsGSN .fer w ν Ψ)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) : 0 < ext (rhoHat .fer Ψ) t0 :=
  rhoHat_pos_of_ucp hw (fun _ h => gsN_ne_zero_fer hw h) hΨ ht0

/-- **Ground-state densities of measure potentials are positive on `(0, 1)`**, for bosons or
fermions and any continuous interaction: a density with an interior zero is not `v`-representable
even with measure potentials. -/
theorem vrepMeasN_pos {τ : Stat} {ρ : Pot} (hw : Continuous w) (h : VRepMeasN τ n w ρ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < ext ρ t := by
  obtain ⟨μp, μm, _, _, Φ, hΦ, rfl⟩ := h
  cases τ with
  | bos => exact rhoHat_pos_bos hw hΦ ht
  | fer => exact rhoHat_pos_fer hw hΦ ht

end DFT.Continuum.Line
