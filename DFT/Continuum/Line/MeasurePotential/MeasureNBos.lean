/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureChar
import DFT.Continuum.Line.MeasurePotential.MeasureN

/-!
# Non-interacting bosons in a measure potential

For `w = 0` the `N`-particle problem in a measure potential reduces to one particle:

* `QMN_ge_EM` (any statistics): `T(Ψ) + ν(ρ̂_Ψ) ≥ N E₀(ν)`, because `√ρ̂_Ψ` has kinetic
  energy at most `T(Ψ)` and norm `N` (Hoffmann-Ostenhof);
* `kinW_prodS`, `rhoHat_prodS`, `QMN_prodS`: the product `Π g(x_k)` of a one-particle ground state
  has energy `N E₀` and density `N g²`, so it is an `N`-boson ground state (`isGSN_prodS`);
* `gs1_of_isGSN`: conversely, the density of every `N`-boson ground state is `N g²` with `g` a
  one-particle ground state.

* **`vrepMeasN_bos_iff`**: for non-interacting bosons, `ρ` is the ground-state density of a measure
  potential iff `ρ / N` is a one-particle one (`vrepMeas_iff_explicit` makes this explicit).
* **`trap_vrepMeasN`**: the plateau density `N (c trapG)²` is the ground-state density of `N`
  non-interacting bosons in `-3δ_{1/3} - 3δ_{2/3}` (it is not `v`-representable with continuous
  potentials, `trap_nrep_not_vrep`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### The lower bound -/

lemma QMN_zero (τ : Stat) (ν : PotM) (Φ : Cfg n → ℝ) :
    QMN τ 0 ν Φ = kinW Φ + ν (rhoHat τ Φ) := by
  simp [QMN, h0W_self]

/-- **`T(Ψ) + ν(ρ̂_Ψ) ≥ N E₀(ν)`** for every normalised state, bosons or fermions. -/
theorem QMN_ge_EM {τ : Stat} (ν : PotM) {Ψ : Cfg n → ℝ} (h : Ψ ∈ DomW τ n)
    (hn : ∫ x, Ψ x ^ 2 ∂μN n = 1) : (n + 1) * EM ν ≤ QMN τ 0 ν Ψ := by
  have hg := h10_gN (τ := τ) Ψ
  have h1 := EM_mul_le ν hg
  rw [integral_gN_sq h, hn, mul_one] at h1
  rw [QMN_zero]
  have h2 : QM ν hg ≤ kinW Ψ + ν (rhoHat τ Ψ) := by
    rw [QM]; have := kinM_gN_le h; rw [rhoHat]; linarith
  linarith [mul_comm (EM ν) ((n : ℝ) + 1)]

/-! ### Product states -/

section prod

variable {g : ℝ → ℝ}

lemma kinW_prodS (hg : H10 g) (hn : ∫ t, g t ^ 2 ∂μ1 = 1) :
    kinW (prodS (n := n) g) = (n + 1) * kinM g := by
  have hk : ∀ k : Fin (n + 1), ∫ x, dW k (prodS (n := n) g) x * dW k (prodS g) x ∂μN n =
      kinM g := fun k => by
    have hd := dW_ae_eq (isWD_tens (n := n) (fun _ => hg) k)
    rw [← prodS_eq_tens] at hd
    have e : (fun x : Cfg n => dW k (prodS g) x * dW k (prodS g) x) =ᵐ[μN n] fun x =>
        ∏ i, (if i = k then fun t => deriv g t ^ 2 else fun t => g t ^ 2) (x i) := by
      filter_upwards [hd] with x hx
      rw [hx, tens, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = k
      · subst hi; simp [sq]
      · simp [hi, sq]
    rw [integral_congr_ae e, integral_prod_cube]
    simp only [apply_ite (fun f : ℝ → ℝ => ∫ t, f t ∂μ1), hn]
    rw [Finset.prod_eq_single k (fun i _ hi => ite_eq_right hi)
      (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]
    rfl
  simp only [kinW, hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

lemma rhoHat_prodS (hg : H10 g) (hgc : Continuous g) (hn : ∫ t, g t ^ 2 ∂μ1 = 1) :
    rhoHat .bos (prodS (n := n) g) = ((n : ℝ) + 1) • sqP hg := by
  have hmem := prodS_memW (n := n) hg hgc
  refine rhoHat_unique hmem fun v => ?_
  have h1 := dens_eq_rhoNW (w := (0 : Cfg n → ℝ)) (hw := continuous_const) hmem v
  have h2 := dens_prodS (n := n) hgc hn v
  change ∫ x, LN n v x * (prodS g x * prodS g x) ∂μN n = _ at h1
  rw [← h1, h2]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp [SturmLiouville.ext, projIcc_of_mem _ (Ioo_subset_Icc_self ht)]

lemma QMN_prodS (ν : PotM) (hg : H10 g) (hgc : Continuous g) (hn : ∫ t, g t ^ 2 ∂μ1 = 1) :
    QMN .bos 0 ν (prodS (n := n) g) = (n + 1) * QM ν hg := by
  rw [QMN_zero, kinW_prodS hg hn, rhoHat_prodS hg hgc hn, map_smul, smul_eq_mul, QM]; ring

lemma norm_prodS (hn : ∫ t, g t ^ 2 ∂μ1 = 1) : ∫ x, prodS (n := n) g x ^ 2 ∂μN n = 1 := by
  have := ip_prodS (n := n) hn
  simp only [ip] at this
  rw [← this]; simp_rw [sq]

/-- **The product of a one-particle ground state is an `N`-boson ground state.** -/
theorem isGSN_prodS (ν : PotM) (hg : H10 g) (hgc : Continuous g) (hn : ∫ t, g t ^ 2 ∂μ1 = 1)
    (hmin : QM ν hg = EM ν) : IsGSN .bos 0 ν (prodS (n := n) g) :=
  ⟨prodS_memW hg hgc, norm_prodS hn, fun Ψ hΨ hΨn => by
    rw [QMN_prodS ν hg hgc hn, hmin]; exact QMN_ge_EM ν hΨ hΨn⟩

end prod

/-- A continuous normalised one-particle ground state. -/
lemma exists_min_cont (ν : PotM) :
    ∃ g : ℝ → ℝ, ∃ hg : H10 g, Continuous g ∧ ∫ t, g t ^ 2 ∂μ1 = 1 ∧ QM ν hg = EM ν := by
  obtain ⟨ψ, hψ, hn, hmin⟩ := exists_min ν
  refine ⟨_, H10.clamp_H10 hψ, H10.continuous_clamp hψ, ?_, (QM_clamp ν hψ).trans hmin⟩
  rw [integral_mu1_clamp (F := fun _ y => y ^ 2)]; exact hn

/-- `N`-boson ground states in a measure potential exist (`w = 0`). -/
theorem exists_isGSN_bos (ν : PotM) : ∃ Φ : Cfg n → ℝ, IsGSN .bos 0 ν Φ := by
  obtain ⟨g, hg, hgc, hn, hmin⟩ := exists_min_cont ν
  exact ⟨_, isGSN_prodS ν hg hgc hn hmin⟩

/-- The `N`-boson ground-state energy is `N E₀`. -/
lemma QMN_isGSN {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN .bos 0 ν Φ) :
    QMN .bos 0 ν Φ = (n + 1) * EM ν := by
  obtain ⟨g, hg, hgc, hn, hmin⟩ := exists_min_cont ν
  refine le_antisymm ?_ (QMN_ge_EM ν h.1 h.2.1)
  have := h.2.2 _ (prodS_memW (n := n) hg hgc) (norm_prodS hn)
  rwa [QMN_prodS ν hg hgc hn, hmin] at this

/-- **The density of an `N`-boson ground state is `N g²`, `g` a one-particle ground state.** -/
theorem gs1_of_isGSN {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN .bos 0 ν Φ) :
    ∃ g : ℝ → ℝ, ∃ hg : H10 g, ∫ t, g t ^ 2 ∂μ1 = 1 ∧ QM ν hg = EM ν ∧
      rhoHat .bos Φ = ((n : ℝ) + 1) • sqP hg := by
  have hG := h10_gN (τ := .bos) Φ
  have hN : (0 : ℝ) < n + 1 := by positivity
  set c := 1 / √((n : ℝ) + 1)
  have hc2 : c ^ 2 = 1 / ((n : ℝ) + 1) := by rw [div_pow, Real.sq_sqrt hN.le, one_pow]
  have hgn : ∫ t, gN .bos Φ t ^ 2 ∂μ1 = n + 1 := by rw [integral_gN_sq h.1, h.2.1, mul_one]
  have hn : ∫ t, (c * gN .bos Φ t) ^ 2 ∂μ1 = 1 := by
    rw [norm2_smul, hc2, hgn, one_div_mul_cancel hN.ne']
  have hQ : QM ν hG ≤ (n + 1) * EM ν := by
    rw [← QMN_isGSN h, QMN_zero, QM]
    have := kinM_gN_le h.1; rw [rhoHat]; linarith
  refine ⟨_, hG.const_mul c, hn, le_antisymm ?_ (EM_le ν _ hn), ?_⟩
  · rw [QM_smul ν hG c, hc2]
    calc 1 / ((n : ℝ) + 1) * QM ν hG ≤ 1 / ((n : ℝ) + 1) * ((n + 1) * EM ν) :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = EM ν := by field_simp
  · rw [sqP_smul, smul_smul, hc2, mul_one_div_cancel hN.ne', one_smul]; rfl

/-- **Non-interacting bosons in a measure potential**: `ρ` is an `N`-boson ground-state density iff
`ρ / N` is a one-particle ground-state density. -/
theorem vrepMeasN_bos_iff (ρ : Pot) :
    VRepMeasN .bos n 0 ρ ↔ ∃ ρ1 : Pot, VRepMeas ρ1 ∧ ρ = ((n : ℝ) + 1) • ρ1 := by
  constructor
  · rintro ⟨μp, μm, _, _, Φ, hΦ, rfl⟩
    obtain ⟨g, hg, hn, hmin, hρ⟩ := gs1_of_isGSN hΦ
    exact ⟨sqP hg, ⟨μp, μm, inferInstance, inferInstance, g, isGSM_of_min hg hn hmin, hn,
      fun _ => rfl⟩, hρ⟩
  · rintro ⟨ρ1, ⟨μp, μm, _, _, ψ, hgs, hn, hρ1⟩, rfl⟩
    have hψ := hgs.1
    have hmin := QM_eq_EM_of_isGSM hgs hn hψ
    have hgc := H10.clamp_H10 hψ
    have hn' : ∫ t, H10.clamp ψ t ^ 2 ∂μ1 = 1 := by
      rw [integral_mu1_clamp (F := fun _ y => y ^ 2)]; exact hn
    refine ⟨μp, μm, inferInstance, inferInstance, _,
      isGSN_prodS _ hgc (H10.continuous_clamp hψ) hn' ((QM_clamp _ hψ).trans hmin), ?_⟩
    rw [rhoHat_prodS hgc (H10.continuous_clamp hψ) hn']
    congr 1
    ext t
    rw [sqP_apply, hρ1 t, H10.clamp_eq t.2]

/-! ### Example: the plateau density for `N` bosons -/

instance : IsMeas01 (0 : Measure ℝ) where
  compl_zero := rfl

lemma isMeas01_dirac {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : IsMeas01 (Measure.dirac t) where
  compl_zero := by
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl]; simp [ht]

lemma intCLM_dirac {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    @intCLM (Measure.dirac t) (isMeas01_dirac ht).toIsFiniteMeasure = deltaM ⟨t, ht⟩ := by
  ext h
  rw [intCLM_apply, integral_dirac]
  simp [SturmLiouville.ext, projIcc_of_mem _ ht, deltaM]

/-- **The plateau density is the ground-state density of `N` non-interacting bosons** in a
measure potential (`-3δ_{1/3} - 3δ_{2/3}`). -/
theorem trap_vrepMeasN : VRepMeasN .bos n 0 (((n : ℝ) + 1) • trapP) := by
  refine (vrepMeasN_bos_iff _).2 ⟨trapP, ?_, rfl⟩
  have h13 : (1 / 3 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h23 : (2 / 3 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := isMeas01_dirac h13
  have := isMeas01_dirac h23
  set μm : Measure ℝ := (3 : NNReal) • Measure.dirac (1 / 3) + (3 : NNReal) • Measure.dirac (2 / 3)
  have hν : nuOf 0 μm = nuTrap := by
    ext h
    simp only [nuOf, sub_apply, intCLM_apply, integral_zero_measure, zero_sub, μm, nuTrap]
    rw [integral_add_measure (integrable_ext _ h) (integrable_ext _ h),
      integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_dirac, integral_dirac,
      SturmLiouville.ext, SturmLiouville.ext, projIcc_of_mem _ h13, projIcc_of_mem _ h23]
    simp only [NNReal.smul_def, smul_eq_mul, deltaM, smul_apply, ContinuousMap.evalCLM_apply,
      NNReal.coe_ofNat]
    ring
  obtain ⟨hgs, -⟩ := trap_isGSM
  refine ⟨0, μm, inferInstance, inferInstance, fun t => cTrap 0 * trapG t, ?_, ?_, fun _ => rfl⟩
  · rw [hν]; exact hgs.const_mul (cTrap_ne 0)
  · rw [norm2_smul, cTrap_sq, div_mul_cancel₀ _ integral_trapG_sq_pos.ne']; norm_num

end DFT.Continuum.Line
