/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Regularity.Kink

/-!
# One particle with measure potentials

The continuous potentials `C([0, 1])` are too few: the ground-state densities they produce are `C¹`
(`gs_dens_C1_stat`), so a kinked density is never `v`-representable (`kink_nrep_not_vrep`). Here the
potentials are enlarged to the continuous linear functionals on `C([0, 1])`, i.e. the finite signed
measures (by Riesz), δ-functions included. A potential `ν` acts on a state `ψ ∈ H¹₀` through
`ν(ψ²)`, which makes sense because `ψ` is continuous.

For one particle with walls at `0` and `1`:

* `PotM`, `sqP`, `kinM`, `QM`, `IsGSM`, `VRepM`: potentials, energy, ground states and
  `v`-representability.
* `sq_le_interval`: Cauchy–Schwarz `(∫_a^b f)² ≤ (b - a) ∫_a^b f²`.
* **`four_sq_half_le`**: `4 φ(½)² ≤ ∫ φ'²` for `φ ∈ H¹₀(0, 1)` (sharp, equality for the tent).
* **`tent_isGSM`**: the tent `1 - 2|t - ½|` is the ground state of `-d²/dt² - 4δ_{½}`, with energy
  `0`.
* **`kink_vrepM_not_vrep`**: the kinked density `∝ (1 - 2|t - ½|)²` is `v`-representable with a
  measure potential, but not with any continuous potential.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

/-- Measure potentials: continuous linear functionals on `C([0, 1])` (finite signed measures). -/
abbrev PotM : Type := StrongDual ℝ Pot

/-- The δ-function at `t ∈ [0, 1]`. -/
noncomputable def deltaM (t : Icc (0 : ℝ) 1) : PotM := ContinuousMap.evalCLM ℝ t

/-- `ψ²` as a continuous function on `[0, 1]`. -/
noncomputable def sqP {ψ : ℝ → ℝ} (hψ : H10 ψ) : Pot :=
  ⟨fun t => ψ t ^ 2, (hψ.continuousOn.pow 2).domRestrict⟩

@[simp] lemma sqP_apply {ψ : ℝ → ℝ} (hψ : H10 ψ) (t : Icc (0 : ℝ) 1) : sqP hψ t = ψ t ^ 2 := rfl

/-- The kinetic energy `∫ ψ'²`. -/
noncomputable def kinM (ψ : ℝ → ℝ) : ℝ := ∫ t, deriv ψ t ^ 2 ∂μ1

/-- The energy `∫ ψ'² + ν(ψ²)`. -/
noncomputable def QM (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) : ℝ := kinM ψ + ν (sqP hψ)

/-- `ψ` is a ground state of `-d²/dt² + ν`: a nonzero minimiser of the Rayleigh quotient on
`H¹₀(0, 1)`. -/
def IsGSM (ν : PotM) (ψ : ℝ → ℝ) : Prop :=
  ∃ hψ : H10 ψ, 0 < ∫ t, ψ t ^ 2 ∂μ1 ∧
    ∀ φ (hφ : H10 φ), QM ν hψ * ∫ t, φ t ^ 2 ∂μ1 ≤ QM ν hφ * ∫ t, ψ t ^ 2 ∂μ1

/-- `ρ ∈ C([0, 1])` is the density of a normalised ground state of a measure potential. -/
def VRepM (ρ : Pot) : Prop :=
  ∃ ν ψ, IsGSM ν ψ ∧ ∫ t, ψ t ^ 2 ∂μ1 = 1 ∧ ∀ t : Icc (0 : ℝ) 1, ρ t = ψ t ^ 2

/-! ### Cauchy–Schwarz and the sharp inequality at `½` -/

lemma sq_le_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  set I := ∫ t in a..b, f t
  set J := ∫ t in a..b, f t ^ 2
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp [I]
  · have hpos : 0 < b - a := sub_pos.2 h
    set m := I / (b - a)
    have h0 : 0 ≤ ∫ t in a..b, (f t - m) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
    have i1 : IntervalIntegrable (fun t => f t ^ 2 - 2 * m * f t) volume a b :=
      hf2.sub (hf.const_mul _)
    have hexp : ∫ t in a..b, (f t - m) ^ 2 = J - 2 * m * I + m ^ 2 * (b - a) := by
      have : (fun t => (f t - m) ^ 2) = fun t => (f t ^ 2 - 2 * m * f t) + m ^ 2 := by
        funext t; ring
      rw [this, intervalIntegral.integral_add i1 intervalIntegrable_const,
        intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have e2 : J - 2 * m * I + m ^ 2 * (b - a) = J - I ^ 2 / (b - a) := by
      simp only [m]; field_simp; ring
    rw [hexp, e2] at h0
    have h3 : I ^ 2 / (b - a) ≤ J := by linarith
    rw [div_le_iff₀ hpos] at h3
    linarith

/-- **`4 φ(½)² ≤ ∫ φ'²`** for `φ ∈ H¹₀(0, 1)`. -/
theorem four_sq_half_le {φ : ℝ → ℝ} (hφ : H10 φ) : 4 * φ (1 / 2) ^ 2 ≤ kinM φ := by
  have hac := hφ.1
  have hd2 : IntegrableOn (fun t => deriv φ t ^ 2) (Ioo (0 : ℝ) 1) := hφ.2.2.2
  have hii : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => deriv φ t ^ 2) volume a b := fun ha hab hb =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 (hd2.mono_set (Ioo_subset_Ioo ha hb))
  have hid : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable (deriv φ) volume a b :=
    fun ha hab hb => (hac.mono (by
      rw [uIcc01, uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable_deriv
  have acL : AbsolutelyContinuousOnInterval φ 0 (1 / 2) := hac.mono (by
    rw [uIcc01, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have acR : AbsolutelyContinuousOnInterval φ (1 / 2) 1 := hac.mono (by
    rw [uIcc01, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have hL : φ (1 / 2) = ∫ t in (0 : ℝ)..(1 / 2), deriv φ t := by
    rw [acL.integral_deriv_eq_sub, hφ.2.1, sub_zero]
  have hR : φ (1 / 2) = -∫ t in (1 / 2 : ℝ)..1, deriv φ t := by
    rw [acR.integral_deriv_eq_sub, hφ.2.2.1]
    ring
  have cL := sq_le_interval (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (hid le_rfl (by norm_num) (by norm_num)) (hii le_rfl (by norm_num) (by norm_num))
  have cR := sq_le_interval (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (hid (by norm_num) (by norm_num) le_rfl) (hii (by norm_num) (by norm_num) le_rfl)
  rw [← hL] at cL
  rw [show (∫ t in (1 / 2 : ℝ)..1, deriv φ t) = -φ (1 / 2) by rw [hR]; ring, neg_sq] at cR
  have hsplit : kinM φ = (∫ t in (0 : ℝ)..(1 / 2), deriv φ t ^ 2) +
      ∫ t in (1 / 2 : ℝ)..1, deriv φ t ^ 2 := by
    rw [kinM, integral_mu1, intervalIntegral.integral_add_adjacent_intervals
      (hii le_rfl (by norm_num) (by norm_num)) (hii (by norm_num) (by norm_num) le_rfl)]
  rw [hsplit]
  linarith

/-! ### The tent is a ground state of `-d² - 4δ_{½}` -/

lemma deriv_tentG_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htm : t ≠ 1 / 2) (c : ℝ) :
    deriv (fun s => c * tentG s) t ^ 2 = 4 * c ^ 2 := by
  rcases lt_or_gt_of_ne htm with h | h
  · have hev : (fun s => c * tentG s) =ᶠ[𝓝 t] fun s => c * (2 * s) := by
      filter_upwards [Ioo_mem_nhds ht.1 h] with s hs
      simp only [tentG, tentF]
      rw [abs_of_neg (by linarith [hs.2]), max_eq_right (by linarith [hs.1])]
      ring
    rw [hev.deriv_eq]
    have : HasDerivAt (fun s : ℝ => c * (2 * s)) (c * (2 * 1)) t :=
      ((hasDerivAt_id t).const_mul 2).const_mul c
    rw [this.deriv]; ring
  · have hev : (fun s => c * tentG s) =ᶠ[𝓝 t] fun s => c * (2 - 2 * s) := by
      filter_upwards [Ioo_mem_nhds h ht.2] with s hs
      simp only [tentG, tentF]
      rw [abs_of_pos (by linarith [hs.1]), max_eq_right (by linarith [hs.2])]
      ring
    rw [hev.deriv_eq]
    have : HasDerivAt (fun s : ℝ => c * (2 - 2 * s)) (c * -(2 * 1)) t :=
      (((hasDerivAt_id t).const_mul 2).const_sub 2).const_mul c
    rw [this.deriv]; ring

lemma kinM_tentG (c : ℝ) : kinM (fun s => c * tentG s) = 4 * c ^ 2 := by
  rw [kinM]
  have hae : ∀ᵐ t ∂μ1, deriv (fun s => c * tentG s) t ^ 2 = 4 * c ^ 2 := by
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 / 2 := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hne] with t ht hne
    exact deriv_tentG_sq ht hne c
  rw [integral_congr_ae hae]
  simp

/-- **The tent is a ground state of `-d²/dt² - 4δ_{½}`** (any nonzero multiple). -/
theorem tent_isGSM {c : ℝ} (hc : c ≠ 0) :
    IsGSM (-4 • deltaM ⟨1 / 2, by norm_num, by norm_num⟩) fun s => c * tentG s := by
  have hH : H10 fun s => c * tentG s := h10_tentG.const_mul c
  have hpos : 0 < ∫ t, (c * tentG t) ^ 2 ∂μ1 := by
    simp only [mul_pow]
    rw [integral_const_mul]
    exact mul_pos (by positivity) integral_tentG_sq_pos
  have hQ : ∀ {φ : ℝ → ℝ} (hφ : H10 φ),
      QM (-4 • deltaM ⟨1 / 2, by norm_num, by norm_num⟩) hφ = kinM φ - 4 * φ (1 / 2) ^ 2 :=
    fun hφ => by
      simp only [QM, smul_apply, deltaM, ContinuousMap.evalCLM_apply,
        sqP_apply]
      ring
  have hQ0 : QM (-4 • deltaM ⟨1 / 2, by norm_num, by norm_num⟩) hH = 0 := by
    rw [hQ, kinM_tentG, show tentG (1 / 2) = 1 from tent_center _ _]; ring
  refine ⟨hH, hpos, fun φ hφ => ?_⟩
  rw [hQ0, zero_mul, hQ]
  exact mul_nonneg (by linarith [four_sq_half_le hφ]) hpos.le

/-! ### Measure potentials represent the kinked density -/

/-- The kinked density for one particle, as a continuous function. -/
noncomputable def kinkP : Pot :=
  ⟨fun t => (cKink 0 * tentG t) ^ 2, ((continuous_const.mul continuous_tentG).pow 2).comp
    continuous_subtype_val⟩

/-- **The kinked density is `v`-representable with a measure potential** (`-4δ_{½}`), but not with
any continuous potential (and continuous `w`): measure potentials are genuinely needed. -/
theorem kink_vrepM_not_vrep {τ : Stat} {w : Cfg 0 → ℝ} {hw : Continuous w} :
    VRepM kinkP ∧ ¬ EnsVRep (settingW τ 0 w hw) (rhoKink 0) := by
  have hI := integral_tentG_sq_pos
  have hc2 : cKink 0 ^ 2 = 1 / ∫ t, tentG t ^ 2 ∂μ1 := by
    rw [cKink, Real.sq_sqrt (by positivity)]; norm_num
  have hc : cKink 0 ≠ 0 := by
    intro h; rw [h] at hc2; simp at hc2; exact hI.ne' hc2.symm
  refine ⟨⟨_, _, tent_isGSM hc, ?_, fun t => rfl⟩, (kink_nrep_not_vrep fun σ x => ?_).2⟩
  · simp only [mul_pow]
    rw [integral_const_mul, hc2, div_mul_cancel₀ _ hI.ne']
  · rw [Subsingleton.elim (α := Equiv.Perm (Fin 1)) σ 1]
    rfl

end DFT.Continuum.Line
