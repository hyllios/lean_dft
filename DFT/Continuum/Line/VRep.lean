/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.WeakHK
import DFT.Continuum.General.VRep

/-!
# `v`-representability on a line

On a lattice, an interior density is always ensemble-`v`-representable, but it can fail to be
pure-state-`v`-representable through degeneracy. On a line the picture is reversed:

* **Ensembles give nothing new** (`ensVRep_iff_line`, `ensDens_iff_W`). The ground state of every
  potential is nondegenerate (`gs_unique_line`, `exists_unique_gs_W`), so every ground-state
  ensemble has the density of the ground state. (An ensemble here is a finite mixture; any density
  matrix supported on a one-dimensional ground-state space is pure anyway.)
* **Regularity and positivity are obstructions instead** (`gs_density`): the density of a ground
  state is `C²`, strictly positive on `(0, 1)` and zero at the walls. Densities that break this are
  `N`-representable but not `v`-representable:
  - `sinDens`, `N · 2 sin²(2πt)`, has a zero at `t = 1/2`. It is the density of a `C²` state
    (`nrep_sinDens`) but of no ground state of any continuous potential (`not_vrep_sinDens`);
  - `tentDens`, `N · 12 min(t, 1-t)²`, has a kink at `t = 1/2`. It is the density of an `H¹₀`
    state (`nrep_tentDens`) but of no `H¹₀` ground state of any potential `v` with
    `Σ_k v(x_k) + w` smooth (`not_vrepW_tentDens`).

Both obstructions are general: `not_pureDens_of_zero` (an interior zero) and
`not_pureDens_of_not_contDiffAt` (a point where the density is not `C²`), with the `H¹₀`
versions `not_pureDensW_of_zero`, `not_pureDensW_of_not_contDiffAt`.

On `H¹₀` the regularity statements need a smooth `Σ_k v(x_k) + w` (`C^{2N}` on the closed cube),
the hypothesis under which ground states are known to be `C²` (`gsW_ae_eq`).
-/

namespace DFT.Continuum

open MeasureTheory

namespace Line

open Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-! ### Ensembles: nondegeneracy makes them pure -/

/-- On a line, all normalised ground states of `v` have the same density. -/
theorem gs_dens_unique (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Φ Ψ : Cfg n → ℝ}
    (hΦ : IsGS (setting τ n w hw) v Φ) (h1 : ip (μ := μN n) Φ Φ = 1)
    (hΨ : IsGS (setting τ n w hw) v Ψ) (h2 : ip (μ := μN n) Ψ Ψ = 1) :
    dens (setting τ n w hw) Φ = dens (setting τ n w hw) Ψ := by
  obtain ⟨c, hc⟩ := gs_unique_line hws hΦ hΨ
  refine dens_eq_of_ae_smul (c := c) ?_ h1 h2
  filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
  rw [hc x (cube_subset hx)]; rfl

/-- **Ensembles give nothing new on a line**: for every potential, the ensemble densities are
exactly the pure ground-state densities. -/
theorem ensDens_iff_line (hws : ∀ σ x, w (pm σ x) = w x) (v : Pot) (ρ : Pot → ℝ) :
    EnsDens (setting τ n w hw) v ρ ↔ PureDens (setting τ n w hw) v ρ :=
  ⟨pureDens_of_ensDens fun _ _ h1 h1' h2 h2' => gs_dens_unique hws h1 h1' h2 h2',
    ensDens_of_pureDens⟩

/-- **Ensemble `v`-representability equals pure-state `v`-representability on a line.** -/
theorem ensVRep_iff_line (hws : ∀ σ x, w (pm σ x) = w x) (ρ : Pot → ℝ) :
    EnsVRep (setting τ n w hw) ρ ↔ PureVRep (setting τ n w hw) ρ :=
  exists_congr fun v => ensDens_iff_line hws v ρ

section W

variable {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- On `H¹₀`, for smooth `Σ_k v(x_k) + w`, the ensemble densities of `v` are its pure
ground-state densities. -/
theorem ensDens_iff_W (ρ : Pot → ℝ) :
    EnsDens (settingW τ n w hw) v ρ ↔ PureDens (settingW τ n w hw) v ρ := by
  obtain ⟨Φ, -, hΦ1, huniq⟩ := exists_unique_gs_W (τ := τ) (hw := hw) hws hF hVF
  refine ⟨pureDens_of_ensDens fun ψ φ hψ hψ1 hφ hφ1 => ?_, ensDens_of_pureDens⟩
  obtain ⟨a, ha⟩ := huniq ψ hψ
  obtain ⟨b, hb⟩ := huniq φ hφ
  rw [dens_eq_of_ae_smul ha hψ1 hΦ1, dens_eq_of_ae_smul hb hφ1 hΦ1]

end W

/-! ### The density of a ground state is `C²` and positive -/

section regular

/-- Differentiation under the integral over the other particles. -/
lemma hasDerivAt_int_cons {G : Cfg n → ℝ} (hG : ContDiff ℝ 1 G) (t0 : ℝ) :
    HasDerivAt (fun t => ∫ y in Cube' n, G (Fin.cons t y))
      (∫ y in Cube' n, dk 0 G (Fin.cons t0 y)) t0 := by
  have hc := hG.continuous
  have hd : Continuous (dk 0 G) := (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨C, hC⟩ := bound_cons hd t0
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Cube' n))
    (F := fun s y => G (Fin.cons s y)) (F' := fun s y => dk 0 G (Fin.cons s y))
    (bound := fun _ => C) (Metric.ball_mem_nhds t0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hc.comp (continuous_cons_right s)).aestronglyMeasurable
  · exact integrableOn_cube' (hc.comp (continuous_cons_right t0))
  · exact (hd.comp (continuous_cons_right t0)).aestronglyMeasurable
  · exact (ae_restrict_mem measurableSet_cube').mono fun y hy s hs => by
      rw [Real.norm_eq_abs]; exact hC s hs y hy
  · exact integrableOn_cube' continuous_const
  · exact ae_of_all _ fun y s _ => hasDerivAt_cons_slice (hG.differentiable one_ne_zero) s y

lemma contDiff_one_int_cons {G : Cfg n → ℝ} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 fun t => ∫ y in Cube' n, G (Fin.cons t y) := by
  have hd : Continuous (dk 0 G) := (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_int_cons hG t).differentiableAt, ?_⟩
  rw [show deriv (fun t => ∫ y in Cube' n, G (Fin.cons t y)) =
    fun t => ∫ y in Cube' n, dk 0 G (Fin.cons t y) from funext fun t =>
      (hasDerivAt_int_cons hG t).deriv]
  exact continuous_integral_cube' (G := fun t y => dk 0 G (Fin.cons t y))
    (hd.comp continuous_cons_pair)

lemma contDiff_two_int_cons {G : Cfg n → ℝ} (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 fun t => ∫ y in Cube' n, G (Fin.cons t y) := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  refine (contDiff_succ_iff_deriv (n := 1)).2
    ⟨fun t => (hasDerivAt_int_cons hG1 t).differentiableAt,
    by simp, ?_⟩
  rw [show deriv (fun t => ∫ y in Cube' n, G (Fin.cons t y)) =
    fun t => ∫ y in Cube' n, dk 0 G (Fin.cons t y) from funext fun t =>
      (hasDerivAt_int_cons hG1 t).deriv]
  exact contDiff_one_int_cons (contDiff_dk hG 0)

/-- **The density of a `C²` state is `C²`.** -/
theorem contDiff_rhoN {Φ : Cfg n → ℝ} (hΦ : Φ ∈ Dom τ n) : ContDiff ℝ 2 (rhoN Φ) :=
  contDiff_const.mul (contDiff_two_int_cons (G := fun x => Φ x ^ 2) (hΦ.1.pow 2))

/-- A configuration `(t, y)` in the open cube with distinct coordinates. -/
lemma exists_inj_cons {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ y ∈ Cube' n, (Fin.cons t y : Cfg n) ∈ Cube n ∧ Function.Injective (Fin.cons t y : Cfg n) := by
  set y : Fin n → ℝ := fun i => t * (((i : ℕ) + 1 : ℝ) / (n + 2))
  have hq : ∀ i : Fin n, 0 < (((i : ℕ) + 1 : ℝ) / (n + 2)) ∧ (((i : ℕ) + 1 : ℝ) / (n + 2)) < 1 :=
    fun i => by
      have hi : ((i : ℕ) : ℝ) < n := by exact_mod_cast i.2
      exact ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩
  have hy : ∀ i, 0 < y i ∧ y i < t := fun i =>
    ⟨mul_pos ht.1 (hq i).1, mul_lt_of_lt_one_right ht.1 (hq i).2⟩
  have hyC : y ∈ Cube' n := fun i _ => ⟨(hy i).1, (hy i).2.trans ht.2⟩
  refine ⟨y, hyC, ?_, ?_⟩
  · intro k _
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using ht
    · simpa using hyC i (mem_univ i)
  · rw [Fin.cons_injective_iff]
    refine ⟨fun ⟨i, hi⟩ => (hy i).2.ne hi, fun i j h => ?_⟩
    have hn : (0 : ℝ) < n + 2 := by positivity
    simp only [y] at h
    have h' := mul_left_cancel₀ ht.1.ne' h
    rw [div_left_inj' hn.ne'] at h'
    exact Fin.ext (by exact_mod_cast (by linarith : ((i : ℕ) : ℝ) = (j : ℕ)))

/-- **The density of a ground state is strictly positive inside the interval.** -/
theorem rhoN_pos (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Φ : Cfg n → ℝ}
    (hΦ : IsGS (setting τ n w hw) v Φ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < rhoN Φ t := by
  obtain ⟨y0, hy0, hx0, hinj⟩ := exists_inj_cons (n := n) ht
  have hne := gs_ne_zero_stat hws hΦ _ hx0 hinj
  have hc : Continuous fun y : Fin n → ℝ => Φ (Fin.cons t y) ^ 2 :=
    (hΦ.1.1.continuous.comp (continuous_cons_right t)).pow 2
  have hm : 0 < marg Φ t := by
    unfold marg
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (integrableOn_cube' hc)]
    have hopen : IsOpen (Function.support (fun y : Fin n → ℝ => Φ (Fin.cons t y) ^ 2) ∩ Cube' n) :=
      (isOpen_ne_fun hc continuous_const).inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
    exact hopen.measure_pos _ ⟨y0, pow_ne_zero 2 hne, hy0⟩
  exact mul_pos (by positivity) hm

/-- **Ground-state densities on a line.** The density `ρ = rhoN Φ` of a normalised ground state of
any continuous potential is `C²`, strictly positive on `(0, 1)`, zero at the walls, integrates to
`N`, and is the density functional of `Φ`. -/
theorem gs_density (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Φ : Cfg n → ℝ}
    (hΦ : IsGS (setting τ n w hw) v Φ) (h1 : ip (μ := μN n) Φ Φ = 1) :
    ContDiff ℝ 2 (rhoN Φ) ∧ (∀ t ∈ Ioo (0 : ℝ) 1, 0 < rhoN Φ t) ∧
      rhoN Φ 0 = 0 ∧ rhoN Φ 1 = 0 ∧ ∫ t in Ioo (0 : ℝ) 1, rhoN Φ t = n + 1 ∧
      dens (setting τ n w hw) Φ = fun u => ∫ t in Ioo (0 : ℝ) 1, ext u t * rhoN Φ t := by
  obtain ⟨-, h0, h1', hint, -⟩ := sqrt_dens_H1 hΦ.1
  refine ⟨contDiff_rhoN hΦ.1, fun t ht => rhoN_pos hws hΦ ht, h0, h1', ?_,
    funext fun u => dens_eq_rhoN hΦ.1 u⟩
  rw [hint, show ∫ x, Φ x ^ 2 ∂μN n = 1 by rw [← h1]; simp only [ip, sq], mul_one]

end regular

/-! ### Obstructions -/

section obstruct

/-- A density functional `v ↦ ∫₀¹ v f` with continuous `f` determines `f` on `(0, 1)`. -/
lemma eqOn_of_integral_pot {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ u : Pot, ∫ t in Ioo (0 : ℝ) 1, ext u t * f t = ∫ t in Ioo (0 : ℝ) 1, ext u t * g t) :
    EqOn f g (Ioo 0 1) := by
  set u : Pot := ⟨fun s => f s - g s, (hf.sub hg).comp continuous_subtype_val⟩
  have hu : ∀ t, ext u t = f (projIcc 0 1 zero_le_one t) - g (projIcc 0 1 zero_le_one t) :=
    fun _ => rfl
  have hint : ∀ k : ℝ → ℝ, Continuous k → IntegrableOn (fun t => ext u t * k t) (Ioo (0 : ℝ) 1) :=
    fun k hk => (((continuous_ext u).mul hk).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hz : ∫ t in Ioo (0 : ℝ) 1, (f t - g t) * (f t - g t) = 0 := by
    have e : ∫ t in Ioo (0 : ℝ) 1, (f t - g t) * (f t - g t) =
        ∫ t in Ioo (0 : ℝ) 1, (ext u t * f t - ext u t * g t) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      simp only [hu, projIcc_of_mem _ (Ioo_subset_Icc_self ht)]; ring
    rw [e, integral_sub (hint f hf) (hint g hg), h u, sub_self]
  have hc : Continuous fun t => (f t - g t) * (f t - g t) := (hf.sub hg).mul (hf.sub hg)
  have hae : (fun t => (f t - g t) * (f t - g t)) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => mul_self_nonneg _)
      ((hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self)).1 hz
  have hz' := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hc.continuousOn continuousOn_const
  exact fun t ht => sub_eq_zero.1 (mul_self_eq_zero.1 (hz' ht))

/-- A ground state with density functional `v ↦ ∫₀¹ v f` has `rhoN = f` on `(0, 1)`. -/
lemma rhoN_eqOn {Φ : Cfg n → ℝ} (hΦ : Φ ∈ Dom τ n) {f : ℝ → ℝ} (hf : Continuous f)
    (h : dens (setting τ n w hw) Φ = fun u => ∫ t, ext u t * f t ∂μ1) :
    EqOn (rhoN Φ) f (Ioo 0 1) :=
  eqOn_of_integral_pot (contDiff_rhoN hΦ).continuous hf fun u => by
    rw [← dens_eq_rhoN (w := w) (hw := hw) hΦ u, h]

variable (hws : ∀ σ x, w (pm σ x) = w x) {f : ℝ → ℝ} (hf : Continuous f)
include hws hf

/-- **An interior zero obstructs `v`-representability.** -/
theorem not_pureDens_of_zero {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) (hz : f t0 = 0) (v : Pot) :
    ¬ PureDens (setting τ n w hw) v fun u => ∫ t, ext u t * f t ∂μ1 := by
  rintro ⟨Φ, hΦ, -, hd⟩
  have := rhoN_pos hws hΦ ht0
  rw [rhoN_eqOn hΦ.1 hf hd ht0, hz] at this
  exact lt_irrefl _ this

omit hws in
/-- **A point where the density is not `C²` obstructs `v`-representability.** -/
theorem not_pureDens_of_not_contDiffAt {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1)
    (hnd : ¬ ContDiffAt ℝ 2 f t0) (v : Pot) :
    ¬ PureDens (setting τ n w hw) v fun u => ∫ t, ext u t * f t ∂μ1 := by
  rintro ⟨Φ, hΦ, -, hd⟩
  have hev : rhoN Φ =ᶠ[𝓝 t0] f :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht0) (rhoN_eqOn hΦ.1 hf hd)
  exact hnd (((contDiff_rhoN hΦ.1).contDiffAt).congr_of_eventuallyEq hev.symm)

omit hf in
/-- On `H¹₀`, for smooth `Σ_k v(x_k) + w`, every ground-state density is that of a `C²` ground
state. -/
lemma pureDens_of_W {v : Pot} {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
    (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) {ρ : Pot → ℝ}
    (h : PureDens (settingW τ n w hw) v ρ) : PureDens (setting τ n w hw) v ρ := by
  obtain ⟨Ψ, hΨ, h1, rfl⟩ := h
  obtain ⟨Φ, hΦ, hae⟩ := gsW_ae_eq hws hF hVF hΨ
  have hip : ip (μ := μN n) Φ Φ = 1 := by
    rw [← h1]; exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  have hd : dens (setting τ n w hw) Φ = dens (settingW τ n w hw) Ψ :=
    (dens_eq_of_ae_smul (S := settingW τ n w hw) (c := 1)
      (hae.mono fun x hx => by rw [hx, one_smul]) h1 hip).symm
  exact ⟨Φ, hΦ, hip, hd⟩

theorem not_pureDensW_of_zero {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) (hz : f t0 = 0) {v : Pot}
    {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
    (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ¬ PureDens (settingW τ n w hw) v fun u => ∫ t, ext u t * f t ∂μ1 := fun h =>
  not_pureDens_of_zero hws hf ht0 hz v (pureDens_of_W hws hF hVF h)

theorem not_pureDensW_of_not_contDiffAt {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1)
    (hnd : ¬ ContDiffAt ℝ 2 f t0) {v : Pot} {F : Cfg n → ℝ}
    (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F) (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x) :
    ¬ PureDens (settingW τ n w hw) v fun u => ∫ t, ext u t * f t ∂μ1 := fun h =>
  not_pureDens_of_not_contDiffAt hf ht0 hnd v (pureDens_of_W hws hF hVF h)

end obstruct

/-! ### Two `N`-representable densities that are not `v`-representable -/

section examples

/-- `N · 2 sin²(2πt)`: smooth, but zero at `t = 1/2`. -/
noncomputable def sinDens (n : ℕ) (t : ℝ) : ℝ := (n + 1) * (√2 * Real.sin (2 * π * t)) ^ 2

/-- `N · 12 min(t, 1 - t)²`: positive inside, but with a kink at `t = 1/2`. -/
noncomputable def tentDens (n : ℕ) (t : ℝ) : ℝ := (n + 1) * (√12 * min t (1 - t)) ^ 2

lemma sinG_mem : (fun t => √2 * Real.sin (2 * π * t)) ∈ Box.Dom := by
  refine ⟨by fun_prop, by simp, ?_⟩
  simp only [mul_one, Real.sin_two_pi, mul_zero]

lemma sinG_norm : ∫ t, (√2 * Real.sin (2 * π * t)) ^ 2 ∂μ1 = 1 := by
  rw [integral_mu1]
  simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) (by positivity : 2 * π ≠ 0),
    integral_sin_sq]
  simp only [mul_zero, mul_one, Real.sin_zero, Real.sin_two_pi, zero_mul, sub_zero, smul_eq_mul]
  field_simp
  ring

lemma tent_lip (s t : ℝ) : |min s (1 - s) - min t (1 - t)| ≤ |s - t| := by
  have := abs_min_sub_min_le_max s (1 - s) t (1 - t)
  rwa [show 1 - s - (1 - t) = -(s - t) by ring, abs_neg, max_self] at this

lemma tentG_lip : LipschitzWith (Real.toNNReal √12) fun t : ℝ => √12 * min t (1 - t) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), ← mul_sub, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (tent_lip s t) (Real.sqrt_nonneg _)

lemma tentG_mem : H10 fun t => √12 * min t (1 - t) := by
  refine ⟨(tentG_lip.lipschitzOnWith).absolutelyContinuousOnInterval, by simp, by simp, ?_⟩
  have hb : ∀ t, ‖deriv (fun t : ℝ => √12 * min t (1 - t)) t ^ 2‖ ≤ 12 := fun t => by
    have h := norm_deriv_le_of_lipschitz (x₀ := t) tentG_lip
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.norm_eq_abs] at h
    rw [Real.norm_eq_abs, abs_pow]
    calc |deriv (fun t : ℝ => √12 * min t (1 - t)) t| ^ 2 ≤ √12 ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 12 := Real.sq_sqrt (by norm_num)
  exact (integrableOn_const (C := (12 : ℝ)) (by simp)).mono'
    ((measurable_deriv _).pow_const 2).aestronglyMeasurable (ae_of_all _ hb)

lemma tentG_norm : ∫ t, (√12 * min t (1 - t)) ^ 2 ∂μ1 = 1 := by
  rw [integral_mu1]
  have hc : Continuous fun t : ℝ => (√12 * min t (1 - t)) ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h12 : (√12 : ℝ) ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have h1 : ∫ t in (0 : ℝ)..1 / 2, (√12 * min t (1 - t)) ^ 2 =
      ∫ t in (0 : ℝ)..1 / 2, 12 * t ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [min_eq_left (by linarith [ht.2] : t ≤ 1 - t), mul_pow, h12]
  have h2 : ∫ t in (1 / 2 : ℝ)..1, (√12 * min t (1 - t)) ^ 2 =
      ∫ t in (1 / 2 : ℝ)..1, 12 * (1 - t) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [min_eq_right (by linarith [ht.1] : 1 - t ≤ t), mul_pow, h12]
  have h3 := intervalIntegral.integral_comp_sub_left (fun x : ℝ => 12 * x ^ 2) (a := 1 / 2) (b := 1)
    (1 : ℝ)
  rw [h1, h2, h3]
  norm_num [intervalIntegral.integral_const_mul, integral_pow]

/-- `tentDens` is not differentiable at `1/2`: its one-sided derivatives are `±12 N`. -/
lemma tentDens_not_diff (n : ℕ) : ¬ DifferentiableAt ℝ (tentDens n) (1 / 2) := by
  intro hd
  set A : ℝ := 12 * (n + 1) with hAdef
  have hA : 0 < A := by positivity
  have e : ∀ t, tentDens n t = A * min t (1 - t) ^ 2 := fun t => by
    simp only [tentDens, A, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]; ring
  have hL : HasDerivWithinAt (tentDens n) A (Iic (1 / 2)) (1 / 2) := by
    have h : HasDerivAt (fun t : ℝ => A * t ^ 2) (A * (2 * (1 / 2) ^ 1 * 1)) (1 / 2) :=
      ((hasDerivAt_id (1 / 2 : ℝ)).pow 2).const_mul A
    rw [show A * (2 * (1 / 2 : ℝ) ^ 1 * 1) = A by ring] at h
    refine h.hasDerivWithinAt.congr (fun t ht => ?_) ?_
    · rw [e, min_eq_left (by linarith [mem_Iic.1 ht] : t ≤ 1 - t)]
    · rw [e, min_eq_left (by norm_num : (1 / 2 : ℝ) ≤ 1 - 1 / 2)]
  have hR : HasDerivWithinAt (tentDens n) (-A) (Ici (1 / 2)) (1 / 2) := by
    have h : HasDerivAt (fun t : ℝ => A * (1 - t) ^ 2) (A * (2 * (1 - 1 / 2) ^ 1 * -1)) (1 / 2) :=
      (((hasDerivAt_id (1 / 2 : ℝ)).const_sub 1).pow 2).const_mul A
    rw [show A * (2 * (1 - 1 / 2 : ℝ) ^ 1 * -1) = -A by ring] at h
    refine h.hasDerivWithinAt.congr (fun t ht => ?_) ?_
    · rw [e, min_eq_right (by linarith [mem_Ici.1 ht] : 1 - t ≤ t)]
    · rw [e, min_eq_right (by norm_num : (1 - 1 / 2 : ℝ) ≤ 1 / 2)]
  have hd' := hd.hasDerivAt.hasDerivWithinAt (s := Iic (1 / 2))
  have hd'' := hd.hasDerivAt.hasDerivWithinAt (s := Ici (1 / 2))
  have h1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iic _) hd' hL
  have h2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici _) hd'' hR
  linarith

variable (hws : ∀ σ x, w (pm σ x) = w x)
include hws

/-- **`sinDens` is `N`-representable but not `v`-representable**: it is the density of a
normalised `C²` state, but of no ground state of any continuous potential (the density of a ground
state has no interior zeros). -/
theorem sinDens_not_vrep :
    (∃ ψ ∈ Nst (setting τ n w hw),
        dens (setting τ n w hw) ψ = fun u => ∫ t, ext u t * sinDens n t ∂μ1) ∧
      ¬ PureVRep (setting τ n w hw) fun u => ∫ t, ext u t * sinDens n t ∂μ1 := by
  refine ⟨?_, fun ⟨v, h⟩ => not_pureDens_of_zero hws (by unfold sinDens; fun_prop)
    (t0 := 1 / 2) ⟨by norm_num, by norm_num⟩ ?_ v h⟩
  · obtain ⟨ψ, hψ, hd⟩ : ∃ ψ ∈ Nst (setting τ n w hw), ∀ u, dens (setting τ n w hw) ψ u =
        ∫ t, ext u t * ((n + 1) * (√2 * Real.sin (2 * π * t)) ^ 2) ∂μ1 := by
      cases τ
      · exact ⟨_, (nrep_bos sinG_mem sinG_norm).1, (nrep_bos sinG_mem sinG_norm).2⟩
      · exact nrep_fer sinG_mem sinG_norm
    exact ⟨ψ, hψ, funext hd⟩
  · simp only [sinDens]; rw [show 2 * π * (1 / 2) = π by ring, Real.sin_pi]; ring

/-- **`tentDens` is `N`-representable but not `v`-representable on `H¹₀`**: it is the density of a
normalised `H¹₀` state, but of no `H¹₀` ground state of any `v` with `Σ_k v(x_k) + w` smooth
(ground-state densities are `C²`). -/
theorem tentDens_not_vrep :
    (∃ ψ ∈ Nst (settingW τ n w hw),
        dens (settingW τ n w hw) ψ = fun u => ∫ t, ext u t * tentDens n t ∂μ1) ∧
      ∀ (v : Pot) (F : Cfg n → ℝ), ContDiff ℝ (2 * (n + 1) : ℕ) F →
        (∀ x ∈ CubeC n, LN n v x + w x = F x) →
        ¬ PureDens (settingW τ n w hw) v fun u => ∫ t, ext u t * tentDens n t ∂μ1 := by
  refine ⟨?_, fun v F hF hVF => not_pureDensW_of_not_contDiffAt hws
    (by unfold tentDens; fun_prop) (t0 := 1 / 2) ⟨by norm_num, by norm_num⟩
    (fun h => tentDens_not_diff n (h.differentiableAt (by norm_num))) hF hVF⟩
  obtain ⟨ψ, hψ, hd⟩ := nrepW (τ := τ) (w := w) (hw := hw) tentG_mem tentG_norm
  exact ⟨ψ, hψ, funext hd⟩

end examples

end Line

end DFT.Continuum
