/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.NGS
import DFT.Continuum.Line.Neumann.Dens

/-!
# `N` particles with Neumann walls in an `H⁻¹` potential

An `H⁻¹` potential `v ∈ H¹(0, 1)*` acts on an `N`-particle state through its density, which must
then be an element of `H¹(0, 1)`. For `Φ ∈ H¹` of the cube, `√ρ_Φ` has an `H¹` representative `g`
with `∫ g'² ≤ T(Φ)` (`sqrt_dens_H1N`), so `ρ_Φ = g²` is an element of `H¹(0, 1)`.

* `gNH`, `rhoE`: the density `ρ_Φ = g²` as an element of `H1E`; `rhoE_eq_sqE`: any `H¹`
  representative of `√ρ_Φ` gives the same element. `toE_congr`, `sqE_congr`: `toE` only sees the
  values on `[0, 1]`.
* `QNH`: the energy `T(Φ) + ∫ w Φ² + v(ρ_Φ)`; `IsGSNH`: normalised minimisers among `H¹` states.
* **`abs_v_rhoE_le`** (form bound): `|v(ρ_Φ)| ≤ ½ T(Φ) + C_v N ∫ Φ²`; `QNH_ge`.
* **`exists_isGSNH`**: ground states exist for every `v ∈ H⁻¹`, every continuous `w`, bosons or
  fermions. Direct method in cosine coefficients (`lam_le_lamC` lets the sine compactness lemmas
  apply); the potential term converges by `tendsto_v_dE`, after identifying the uniform limit of
  the `g_j²` with `ρ_Ψ` (`pot_eq_of_integral`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ}

/-! ### `toE` only sees the values on `[0, 1]` -/

lemma toE_congr {g h : ℝ → ℝ} (hg : H1N g) (hh : H1N h) (he : EqOn g h (Icc 0 1)) :
    toE hg = toE hh := by
  have hd : (dN hg : ℝ → ℝ) =ᵐ[vol01] (dN hh : ℝ → ℝ) := by
    filter_upwards [dN_ae hg, dN_ae hh, ae_restrict_mem measurableSet_Ioo] with t h1 h2 ht
    rw [h1, h2]
    exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)
      fun s hs => he (Ioo_subset_Icc_self hs))
  rw [toE, toE, he ⟨le_rfl, zero_le_one⟩, Lp.ext hd]

lemma sqE_congr {g h : ℝ → ℝ} (hg : H1N g) (hh : H1N h)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, g t ^ 2 = h t ^ 2) : sqE hg = sqE hh :=
  toE_congr _ _ fun t ht => by simp only [← sq]; exact he t ht

lemma sqE_eq_of_ae {g h : ℝ → ℝ} (hg : H1N g) (hh : H1N h)
    (he : ∀ᵐ t ∂vol01, g t ^ 2 = h t ^ 2) : sqE hg = sqE hh := by
  have hIoo : EqOn (fun t => g t ^ 2) (fun t => h t ^ 2) (Ioo 0 1) :=
    Measure.eqOn_of_ae_eq he ((hg.continuousOn.pow 2).mono Ioo_subset_Icc_self)
      ((hh.continuousOn.pow 2).mono Ioo_subset_Icc_self)
      (by rw [interior_Ioo]; exact subset_closure)
  have hIcc : EqOn (fun t => g t ^ 2) (fun t => h t ^ 2) (Icc 0 1) :=
    hIoo.of_subset_closure (hg.continuousOn.pow 2) (hh.continuousOn.pow 2) Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  exact sqE_congr hg hh fun t ht => hIcc ht

/-! ### The density as an element of `H¹(0, 1)` -/

variable (τ : Stat)

open Classical in
/-- An `H¹` square root of the density: `g ∈ H¹(0, 1)` with `g² = ρ_Φ` a.e. and
`∫ g'² ≤ T(Φ)`. -/
noncomputable def gNH (Φ : Cfg n → ℝ) : ℝ → ℝ :=
  if h : Φ ∈ DomN τ n then (sqrt_dens_H1N h).choose else fnE 0

variable {τ}

lemma gNH_spec {Φ : Cfg n → ℝ} (h : Φ ∈ DomN τ n) :
    H1N (gNH τ Φ) ∧ (∀ᵐ t ∂vol01, gNH τ Φ t ^ 2 = rhoN Φ t) ∧ kinM (gNH τ Φ) ≤ kinN Φ := by
  simp only [gNH, h, ↓reduceDIte]; exact (sqrt_dens_H1N h).choose_spec

lemma h1N_gNH (Φ : Cfg n → ℝ) : H1N (gNH τ Φ) := by
  by_cases h : Φ ∈ DomN τ n
  · exact (gNH_spec h).1
  · simp only [gNH, h, ↓reduceDIte]; exact h1N_fnE 0

variable (τ)

/-- **The density** `ρ_Φ = g²` as an element of `H1E`. -/
noncomputable def rhoE (Φ : Cfg n → ℝ) : H1E := sqE (h1N_gNH (τ := τ) Φ)

variable {τ}

/-- Any `H¹` square root of the density gives `rhoE`. -/
lemma rhoE_eq_sqE {Φ : Cfg n → ℝ} (h : Φ ∈ DomN τ n) {g : ℝ → ℝ} (hg : H1N g)
    (hρ : ∀ᵐ t ∂vol01, g t ^ 2 = rhoN Φ t) : rhoE τ Φ = sqE hg := by
  refine sqE_eq_of_ae _ hg ?_
  filter_upwards [(gNH_spec h).2.1, hρ] with t h1 h2
  rw [h1, h2]

lemma integral_gNH_sq {Φ : Cfg n → ℝ} (h : Φ ∈ DomN τ n) :
    ∫ t, gNH τ Φ t ^ 2 ∂vol01 = (n + 1) * ∫ x, Φ x ^ 2 ∂μN n := by
  rw [← integral_rhoN h.1]
  exact integral_congr_ae (gNH_spec h).2.1

lemma kinM_gNH_le {Φ : Cfg n → ℝ} (h : Φ ∈ DomN τ n) : kinM (gNH τ Φ) ≤ kinN Φ :=
  (gNH_spec h).2.2

/-! ### The energy -/

variable (τ)

/-- The energy `T(Φ) + ∫ w Φ² + v(ρ_Φ)` of an `N`-particle state with Neumann walls. -/
noncomputable def QNH (w : Cfg n → ℝ) (v : PotH) (Φ : Cfg n → ℝ) : ℝ :=
  kinN Φ + ∫ x, w x * (Φ x * Φ x) ∂μN n + v (rhoE τ Φ)

/-- `Φ` is a normalised ground state of `T + w + v` among `H¹` states of statistics `τ`
(Neumann walls). -/
def IsGSNH (w : Cfg n → ℝ) (v : PotH) (Φ : Cfg n → ℝ) : Prop :=
  Φ ∈ DomN τ n ∧ ∫ x, Φ x ^ 2 ∂μN n = 1 ∧
    ∀ Ψ ∈ DomN τ n, ∫ x, Ψ x ^ 2 ∂μN n = 1 → QNH τ w v Φ ≤ QNH τ w v Ψ

variable {τ}

/-! ### The form bound -/

/-- **Form bound**: `|v(ρ_Φ)| ≤ ½ T(Φ) + C_v N ∫ Φ²`. -/
theorem abs_v_rhoE_le (v : PotH) {Φ : Cfg n → ℝ} (h : Φ ∈ DomN τ n) :
    |v (rhoE τ Φ)| ≤ kinN Φ / 2 + cH v * ((n + 1) * ∫ x, Φ x ^ 2 ∂μN n) := by
  have := abs_v_sq_le v (h1N_gNH (τ := τ) Φ)
  rw [integral_gNH_sq h] at this
  exact this.trans (by linarith [kinM_gNH_le h])

lemma abs_int_w_le {w : Cfg n → ℝ} {B : ℝ} (hB : ∀ᵐ x ∂μN n, ‖w x‖ ≤ B) {Φ : Cfg n → ℝ}
    (hΦ : MemLp Φ 2 (μN n)) (hn : ∫ x, Φ x ^ 2 ∂μN n = 1) :
    |∫ x, w x * (Φ x * Φ x) ∂μN n| ≤ B := by
  have hi := int_mul_L2 hΦ hΦ
  calc |∫ x, w x * (Φ x * Φ x) ∂μN n| ≤ ∫ x, B * (Φ x * Φ x) ∂μN n := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hi.const_mul B) ?_
        filter_upwards [hB] with x hx
        rw [norm_mul, Real.norm_eq_abs (Φ x * Φ x), abs_of_nonneg (mul_self_nonneg _)]
        exact mul_le_mul_of_nonneg_right hx (mul_self_nonneg _)
    _ = B := by
        rw [integral_const_mul]
        have : ∫ x, Φ x * Φ x ∂μN n = 1 := by rw [← hn]; simp_rw [sq]
        rw [this, mul_one]

/-- The energy is bounded below on normalised states, and controls the kinetic energy. -/
theorem QNH_ge {w : Cfg n → ℝ} (hw : Continuous w) (v : PotH) :
    ∃ C, ∀ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 → kinN Φ / 2 - C ≤ QNH τ w v Φ := by
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  refine ⟨cH v * (n + 1) + B, fun Φ h hn => ?_⟩
  have h1 := abs_v_rhoE_le v h
  rw [hn, mul_one] at h1
  have h2 := abs_int_w_le hB h.1 hn
  rw [QNH]
  linarith [neg_abs_le (v (rhoE τ Φ)), neg_abs_le (∫ x, w x * (Φ x * Φ x) ∂μN n)]

/-! ### Existence of ground states -/

lemma cC_sub {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n))
    (m : Fin (n + 1) → ℕ) : cC m (f - g) = cC m f - cC m g := by
  have h1 := int_mul_L2 (memLp_cont (n := n) (continuous_cP m)) hf
  have h2 := int_mul_L2 (memLp_cont (n := n) (continuous_cP m)) hg
  rw [cC, cC, cC, ← integral_sub h1 h2]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)

/-- `∫ u ρ_P = ∫ u (g_P)²` written through `ext (evE (toE g) * evE (toE g))`. -/
lemma integral_ext_evE_sq {Φ : Cfg n → ℝ} (h : Φ ∈ DomN τ n) (u : C01) :
    ∫ t, iccExt u t * iccExt (evE (toE (h1N_gNH (τ := τ) Φ)) * evE (toE (h1N_gNH (τ := τ) Φ))) t ∂vol01 =
      ∫ t, iccExt u t * rhoN Φ t ∂vol01 := by
  refine integral_congr_ae ?_
  filter_upwards [(gNH_spec h).2.1, ae_restrict_mem measurableSet_Ioo] with t h1 ht
  have htI := Ioo_subset_Icc_self ht
  change iccExt u t * (iccExt (evE (toE _)) t * iccExt (evE (toE _)) t) = _
  rw [ext_evE htI, fnE_toE _ htI, ← sq, h1]

/-- `L¹` convergence of `P_k²` gives convergence of `∫ u ρ_{P_k}`. -/
lemma tendsto_int_rhoN (u : C01) {P : ℕ → Cfg n → ℝ} {Ψ : Cfg n → ℝ}
    (hP : ∀ k, MemLp (P k) 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n))
    (hL1 : Tendsto (fun k => ∫ x, |P k x ^ 2 - Ψ x ^ 2| ∂μN n) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t, iccExt u t * rhoN (P k) t ∂vol01) atTop
      (𝓝 (∫ t, iccExt u t * rhoN Ψ t ∂vol01)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ x, |iccExt u x| ≤ ‖u‖ := fun x => by simpa [SturmLiouville.iccExt] using u.norm_coe_le_norm _
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
    (by simpa using (hL1.const_mul ((n + 1) * ‖u‖)))
  have hρi : ∀ (Q : Cfg n → ℝ), MemLp Q 2 (μN n) →
      Integrable (fun t => iccExt u t * rhoN Q t) vol01 := fun Q hQ =>
    ((integrable_marg hQ).const_mul _).bdd_mul (continuous_iccExt u).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa using hb x)
  rw [← integral_sub (hρi _ (hP k)) (hρi _ hΨ)]
  calc ‖∫ t, iccExt u t * rhoN (P k) t - iccExt u t * rhoN Ψ t ∂vol01‖
      ≤ ∫ t, ‖u‖ * |rhoN (P k) t - rhoN Ψ t| ∂vol01 := by
        have hint : Integrable (fun t => ‖u‖ * |rhoN (P k) t - rhoN Ψ t|) vol01 := by
          have h1 : Integrable (rhoN (P k)) vol01 := (integrable_marg (hP k)).const_mul _
          have h2 : Integrable (rhoN Ψ) vol01 := (integrable_marg hΨ).const_mul _
          exact (h1.sub h2).abs.const_mul _
        refine norm_integral_le_of_norm_le hint (ae_of_all _ fun t => ?_)
        rw [← mul_sub, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
    _ = ‖u‖ * ∫ t, |rhoN (P k) t - rhoN Ψ t| ∂vol01 := integral_const_mul _ _
    _ ≤ ‖u‖ * ((n + 1) * ∫ x, |P k x ^ 2 - Ψ x ^ 2| ∂μN n) :=
        mul_le_mul_of_nonneg_left (integral_abs_rhoN_sub (hP k) hΨ) (norm_nonneg _)
    _ = (n + 1) * ‖u‖ * ∫ x, |P k x ^ 2 - Ψ x ^ 2| ∂μN n := by ring

/-- `L¹` convergence of `P_k²` gives convergence of the interaction energy. -/
lemma tendsto_int_w {w : Cfg n → ℝ} (hw : Continuous w) {P : ℕ → Cfg n → ℝ} {Ψ : Cfg n → ℝ}
    (hP : ∀ k, MemLp (P k) 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n))
    (hL1 : Tendsto (fun k => ∫ x, |P k x ^ 2 - Ψ x ^ 2| ∂μN n) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, w x * (P k x * P k x) ∂μN n) atTop
      (𝓝 (∫ x, w x * (Ψ x * Ψ x) ∂μN n)) := by
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (by simpa using hL1.const_mul B)
  have hi : ∀ (Q : Cfg n → ℝ), MemLp Q 2 (μN n) →
      Integrable (fun x => w x * (Q x * Q x)) (μN n) :=
    fun Q hQ => (int_mul_L2 hQ hQ).bdd_mul hw.aestronglyMeasurable hB
  rw [← integral_sub (hi _ (hP k)) (hi _ hΨ)]
  refine (norm_integral_le_of_norm_le
    (((int_sq (hP k)).sub (int_sq hΨ)).abs.const_mul B) ?_).trans
    (by rw [integral_const_mul]; exact le_rfl)
  filter_upwards [hB] with x hx
  rw [← mul_sub, norm_mul, Real.norm_eq_abs (P k x * P k x - Ψ x * Ψ x)]
  rw [show P k x * P k x - Ψ x * Ψ x = P k x ^ 2 - Ψ x ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- **`N`-particle ground states exist with Neumann walls for every `H⁻¹` potential**, every
continuous interaction, bosons or fermions. -/
theorem exists_isGSNH (τ : Stat) {w : Cfg n → ℝ} (hw : Continuous w) (v : PotH) :
    ∃ Φ : Cfg n → ℝ, IsGSNH τ w v Φ := by
  set S := {e | ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ QNH τ w v Φ = e}
  obtain ⟨C, hC⟩ := QNH_ge (τ := τ) hw v
  -- nonempty: a Dirichlet state
  have hSne : S.Nonempty := by
    obtain ⟨a, ha⟩ := exists_adm (n := n) τ
    have hD := serW_mem (s := τ.toSym) ha.toDir
    have hn : ∫ x, serW a x ^ 2 ∂μN n = 1 := by
      rw [← (parsevalW (memLp_serW (a := a))).tsum_eq]
      simp only [cN_serW ha.sq]; exact ha.norm
    exact ⟨_, _, DomWS_le_DomNS _ hD, hn, rfl⟩
  have hbdd : BddBelow S := ⟨-C, fun e ⟨Φ, hΦ, hn, he⟩ => by
    rw [← he]; have := hC Φ hΦ hn; linarith [kinN_nonneg Φ]⟩
  set E := sInf S
  have hE_le : ∀ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 → E ≤ QNH τ w v Φ :=
    fun Φ hΦ hn => csInf_le hbdd ⟨Φ, hΦ, hn, rfl⟩
  -- a minimising sequence
  have hseq : ∀ j : ℕ, ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧
      QNH τ w v Φ < E + 1 / ((j : ℝ) + 1) := fun j => by
    obtain ⟨_, ⟨Φ, hΦ, hn, rfl⟩, h⟩ := exists_lt_of_csInf_lt hSne
      (lt_add_of_pos_right E (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)))
    exact ⟨Φ, hΦ, hn, h⟩
  choose Φ hΦ hΦn hΦE using hseq
  set M := 2 * (E + 1 + C)
  have hkin : ∀ j, kinN (Φ j) ≤ M := fun j => by
    have h1 := hC _ (hΦ j) (hΦn j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith [hΦE j]
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
    have h2' : ∫ s, g j s ^ 2 ∂vol01 = n + 1 := h2
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
  have hv : Tendsto (fun k => v (dE (e (ψ k)))) atTop (𝓝 (v (dE e₀))) :=
    tendsto_v_dE v hfst (fun k => hR _) hwk
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
    have := congrArg (fun P : C01 => P ⟨t, ht⟩) hid
    simp only [ContinuousMap.mul_apply, evE_apply, fnE_toE _ ht] at this
    rw [sq, sq]; exact this
  have hvlim : Tendsto (fun k => v (rhoE τ (Φ (φ (ψ k))))) atTop (𝓝 (v (rhoE τ Ψ))) := by
    rw [← hrho]
    exact hv.congr fun k => by rw [rhoE, sqE_eq_dE]
  -- convergence of the interaction term
  have hwlim := tendsto_int_w hw (fun k => (hΦ (φ (ψ k))).1) hΨ.1 hL1'
  -- the energies converge to `E`
  have hQlim : Tendsto (fun k => QNH τ w v (Φ (φ (ψ k)))) atTop (𝓝 E) := by
    have hz : Tendsto (fun k : ℕ => E + 1 / ((φ (ψ k) : ℝ) + 1)) atTop (𝓝 E) := by
      have := (tendsto_const_nhds (x := E)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (hφ.comp hψ).tendsto_atTop)
      rw [add_zero] at this; exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun k => hE_le _ (hΦ _) (hΦn _)) fun k => (hΦE _).le
  set L := E - ∫ x, w x * (Ψ x * Ψ x) ∂μN n - v (rhoE τ Ψ)
  have hkinlim : Tendsto (fun k => kinN (Φ (φ (ψ k)))) atTop (𝓝 L) := by
    refine ((hQlim.sub hwlim).sub hvlim).congr fun k => ?_
    simp only [QNH]; ring
  -- lower semicontinuity of the kinetic energy
  have hle : ∀ T : Finset (Fin (n + 1) → ℕ), ∑ m ∈ T, lamC m * a m ^ 2 ≤ L := fun T => by
    refine le_of_tendsto_of_tendsto
      (tendsto_finsetSum T fun m _ => (((hlim m).comp hψ.tendsto_atTop).pow 2).const_mul (lamC m))
      hkinlim (Eventually.of_forall fun k => ?_)
    exact sum_lamC_le (h1NW_of_mem (hΦ _)) T
  have hkinΨ : kinN Ψ ≤ L := by
    rw [kinN_serN ha]
    exact Real.tsum_le_of_sum_le (fun m => mul_nonneg (lamC_nonneg m) (sq_nonneg (a m))) hle
  refine ⟨Ψ, hΨ, hΨn, fun Φ' hΦ' hΦ'n => ?_⟩
  have : QNH τ w v Ψ ≤ E := by simp only [QNH]; linarith
  exact this.trans (hE_le Φ' hΦ' hΦ'n)

end DFT.Continuum.Line
