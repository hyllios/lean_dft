/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Lieb
import DFT.Continuum.Box.VRep
import DFT.Continuum.Line.Applications.TonksW

/-!
# One particle on `H¹₀`: `v`-representability is that of the `C²` box

For `N = 1` (`n = 0`) the `H¹₀` setting with continuous `v` and `w` has the same ground-state
densities as the box with `C²` states (`Box.setting`), the interaction `w` acting as an extra
one-body potential `wPot w`. The `H¹₀` ground state is unique up to a factor (`gs_unique_W`) and
the lift of the `C²` box ground state is one, so the exact `C²` characterisation
(`Box.pureVRep_box_iff`) carries over.

* `lift`, `unlift`: `ℝ → ℝ` versus `Cfg 0 → ℝ`; `integral_one`: `∫ F(x₀) dμN = ∫ F dμ1`.
* `isGS_lift`: the lift of a box ground state is a `C²` ground state, hence an `H¹₀` one.
* `isGS_shift`: on `H¹₀`, `w` can be moved into the potential.
* **`pureVRep_one_iff`**: `ρ` is `v`-representable on `H¹₀` iff it is in the box;
  **`pureVRep_one_iff_boxRep`**: iff `ρ(u) = ∫ u g²` with `g` `C²`, positive inside, zero at the
  walls, normalised, and `g''/g` continuous on `[0, 1]`.
* **`not_vrep_one_of_zero`**: a density `∫ u f` with continuous `f` vanishing at an interior
  point is not `v`-representable.
* **`sinDens_nrep_not_vrep`**: `2 sin²(2πt)` (smooth, interior zero) and
  **`quartDens_nrep_not_vrep`**: `30 t² (1 - t)²` (smooth, positive inside, `g''/g` unbounded at
  the walls) are `N`-representable but not `v`-representable on `H¹₀`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {τ : Stat}

/-! ### `Cfg 0` versus `ℝ` -/

/-- A function of one variable as a one-particle wave function. -/
noncomputable def lift (ψ : ℝ → ℝ) (x : Cfg 0) : ℝ := ψ (x 0)

/-- A one-particle wave function as a function of one variable. -/
noncomputable def unlift (Φ : Cfg 0 → ℝ) (t : ℝ) : ℝ := Φ fun _ => t

lemma fin0_eq (i : Fin (0 + 1)) : i = 0 := Fin.fin_one_eq_zero i

lemma sum_fin0 (f : Fin (0 + 1) → ℝ) : ∑ k, f k = f 0 := Fin.sum_univ_one f

lemma cfg0_eq (x : Cfg 0) : (fun _ => x 0 : Cfg 0) = x :=
  funext fun i => by rw [fin0_eq i]

lemma lift_unlift (Φ : Cfg 0 → ℝ) : lift (unlift Φ) = Φ :=
  funext fun x => by simp only [lift, unlift, cfg0_eq]

lemma integral_one (F : ℝ → ℝ) : ∫ x, F (x 0) ∂μN 0 = ∫ t, F t ∂vol01 := by
  have hc : Cube 0 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioo 0 1 := by
    ext x
    simp only [Set.mem_pi, mem_univ, true_implies, mem_preimage, MeasurableEquiv.funUnique_apply]
    exact ⟨fun h => h 0, fun h i => by rw [fin0_eq i]; exact h⟩
  change ∫ x in Cube 0, F (x 0) = ∫ t in Ioo (0 : ℝ) 1, F t
  rw [hc]
  exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) F _

lemma dk_lift {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (x : Cfg 0) :
    dk 0 (lift ψ) x = deriv ψ (x 0) := by
  have hp : HasFDerivAt (fun y : Cfg 0 => y 0)
      (ContinuousLinearMap.proj 0 : Cfg 0 →L[ℝ] ℝ) x := hasFDerivAt_apply 0 x
  have h := (hψ (x 0)).hasDerivAt.comp_hasFDerivAt x hp
  simp only [dk]
  rw [show lift ψ = ψ ∘ fun y : Cfg 0 => y 0 from rfl, h.fderiv]
  simp

lemma ch_one (τ : Stat) : ch τ (1 : Equiv.Perm (Fin 1)) = 1 := by
  cases τ <;> simp [sgn]

lemma lift_mem {ψ : ℝ → ℝ} (hψ : ψ ∈ SturmLiouville.Dom) : lift ψ ∈ Dom τ 0 := by
  refine ⟨hψ.1.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (0 + 1) => ℝ) 0).contDiff,
    fun σ x => ?_, fun x k hk => ?_⟩
  · rw [Subsingleton.elim (α := Equiv.Perm (Fin 1)) σ 1, ch_one]
    simp [lift, pm]
  · rw [fin0_eq k] at hk
    simp only [lift]
    rcases hk with h | h <;> rw [h]
    · exact hψ.2.1
    · exact hψ.2.2

lemma unlift_mem {Φ : Cfg 0 → ℝ} (hΦ : Φ ∈ Dom τ 0) : unlift Φ ∈ SturmLiouville.Dom :=
  ⟨hΦ.1.comp (contDiff_pi.2 fun _ => contDiff_id), hΦ.2.2 _ 0 (Or.inl rfl),
    hΦ.2.2 _ 0 (Or.inr rfl)⟩

lemma ip_lift (ψ φ : ℝ → ℝ) :
    ip (μ := μN 0) (lift ψ) (lift φ) = ip (μ := vol01) ψ φ :=
  integral_one fun t => ψ t * φ t

lemma pf_lift (v : C01) (ψ φ : ℝ → ℝ) :
    ∫ x, LN 0 v x * (lift ψ x * lift φ x) ∂μN 0 = ∫ t, iccExt v t * (ψ t * φ t) ∂vol01 := by
  have : (fun x : Cfg 0 => LN 0 v x * (lift ψ x * lift φ x)) =
      fun x => iccExt v (x 0) * (ψ (x 0) * φ (x 0)) := by
    funext x; simp [LN, lift]
  rw [this]
  exact integral_one fun t => iccExt v t * (ψ t * φ t)

lemma Q_lift {w : Cfg 0 → ℝ} {hw : Continuous w} (hw0 : w = fun _ => 0) (v : C01)
    {ψ : ℝ → ℝ} (hψ : ψ ∈ SturmLiouville.Dom) :
    Q (setting τ 0 w hw) v (lift ψ) = Q Box.setting v ψ := by
  subst hw0
  simp only [Q, pf]
  change h0N 0 (fun _ => 0) (lift ψ) (lift ψ) + ∫ x, LN 0 v x * (lift ψ x * lift ψ x) ∂μN 0 =
    kin ψ ψ + ∫ t, iccExt v t * (ψ t * ψ t) ∂vol01
  rw [pf_lift]
  simp only [h0N, sum_fin0, zero_mul, integral_zero, add_zero, dk_lift (diff_of_mem hψ), kin]
  rw [integral_one fun t => deriv ψ t * deriv ψ t]

lemma dens_lift {w : Cfg 0 → ℝ} {hw : Continuous w} (ψ : ℝ → ℝ) :
    dens (settingW τ 0 w hw) (lift ψ) = dens Box.setting ψ :=
  funext fun v => pf_lift v ψ ψ

/-- **The lift of a box ground state is an `H¹₀` ground state** (no interaction). -/
theorem isGS_lift {v : C01} {φ : ℝ → ℝ} (h : IsGS Box.setting v φ) :
    IsGS (settingW τ 0 (fun _ => 0) continuous_const) v (lift φ) := by
  refine isGS_W_of_isGS ⟨lift_mem h.1, by rw [ip_lift]; exact h.2.1, fun Φ hΦ => ?_⟩
  have hu := unlift_mem hΦ
  have := h.2.2 _ hu
  rw [← Q_lift rfl v h.1, ← Q_lift rfl v hu, ← ip_lift, ← ip_lift, lift_unlift] at this
  exact this

/-! ### The interaction as a one-body potential -/

/-- For one particle, `w` is a potential. -/
noncomputable def wPot (w : Cfg 0 → ℝ) (hw : Continuous w) : C01 :=
  ⟨fun t => w fun _ => (t : ℝ), hw.comp (continuous_pi fun _ => continuous_subtype_val)⟩

lemma LN_wPot {w : Cfg 0 → ℝ} (hw : Continuous w) :
    ∀ᵐ x ∂μN 0, LN 0 (wPot w hw) x = w x := by
  filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
  have hx0 : x 0 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hx 0 trivial)
  simp only [LN, LinearMap.coe_mk, AddHom.coe_mk, sum_fin0, SturmLiouville.iccExt, wPot,
    ContinuousMap.coe_mk, projIcc_of_mem _ hx0]
  rw [cfg0_eq]

variable {w : Cfg 0 → ℝ} {hw : Continuous w}

lemma Q_shift (v : C01) {Ψ : Cfg 0 → ℝ} (hΨ : Ψ ∈ DomW τ 0) :
    Q (settingW τ 0 w hw) v Ψ =
      Q (settingW τ 0 (fun _ => 0) continuous_const) (v + wPot w hw) Ψ := by
  have i1 : Integrable (fun x => LN 0 v x * (Ψ x * Ψ x)) (μN 0) :=
    (settingW τ 0 w hw).int_L v Ψ Ψ hΨ hΨ
  have i2 : Integrable (fun x => LN 0 (wPot w hw) x * (Ψ x * Ψ x)) (μN 0) :=
    (settingW τ 0 w hw).int_L (wPot w hw) Ψ Ψ hΨ hΨ
  simp only [Q, pf]
  change h0W 0 w Ψ Ψ + ∫ x, LN 0 v x * (Ψ x * Ψ x) ∂μN 0 =
    h0W 0 (fun _ => 0) Ψ Ψ + ∫ x, LN 0 (v + wPot w hw) x * (Ψ x * Ψ x) ∂μN 0
  have e : (fun x => LN 0 (v + wPot w hw) x * (Ψ x * Ψ x)) =
      fun x => LN 0 v x * (Ψ x * Ψ x) + LN 0 (wPot w hw) x * (Ψ x * Ψ x) := by
    funext x; rw [map_add, Pi.add_apply, add_mul]
  rw [e, integral_add i1 i2]
  have hw' : ∫ x, w x * (Ψ x * Ψ x) ∂μN 0 = ∫ x, LN 0 (wPot w hw) x * (Ψ x * Ψ x) ∂μN 0 :=
    integral_congr_ae (by filter_upwards [LN_wPot hw] with x hx; rw [hx])
  simp only [h0W, zero_mul, integral_zero, add_zero, hw']
  ring

lemma isGS_shift {v : C01} {Ψ : Cfg 0 → ℝ} :
    IsGS (settingW τ 0 w hw) v Ψ ↔
      IsGS (settingW τ 0 (fun _ => 0) continuous_const) (v + wPot w hw) Ψ := by
  constructor
  · rintro ⟨hD, hp, hmin⟩
    exact ⟨hD, hp, fun φ hφ => by rw [← Q_shift v hD, ← Q_shift v hφ]; exact hmin φ hφ⟩
  · rintro ⟨hD, hp, hmin⟩
    exact ⟨hD, hp, fun φ hφ => by rw [Q_shift v hD, Q_shift v hφ]; exact hmin φ hφ⟩

/-! ### The transfer -/

/-- The density in `settingW` does not depend on the interaction: only the potential coupling
`L = LN 0` enters. (Stated as a lemma so that the kernel never has to compare two settings with
different interactions.) -/
lemma dens_settingW_indep (w w' : Cfg 0 → ℝ) (hw : Continuous w) (hw' : Continuous w')
    (ψ : Cfg 0 → ℝ) : dens (settingW τ 0 w hw) ψ = dens (settingW τ 0 w' hw') ψ := by
  have hL : ∀ (u : Cfg 0 → ℝ) (hu : Continuous u), (settingW τ 0 u hu).L = LN 0 := fun _ _ => rfl
  funext v
  simp only [dens, pf, hL]

/-- **Ground-state densities of one particle on `H¹₀` are those of the box**, the interaction
acting as the potential `wPot w`. -/
theorem pureDens_one_iff (v : C01) (ρ : C01 → ℝ) :
    PureDens (settingW τ 0 w hw) v ρ ↔ PureDens Box.setting (v + wPot w hw) ρ := by
  constructor
  · rintro ⟨Ψ, hΨ, h1, rfl⟩
    have hΨ0 := isGS_shift.1 hΨ
    obtain ⟨φ, hφN⟩ := Box.exists_isNGS (v + wPot w hw)
    have hφ : IsGS Box.setting _ φ :=
      isGS_of_isNGS (fun φ _ _ => integral_nonneg fun t => mul_self_nonneg _) hφN
    have hL := isGS_lift (τ := τ) hφ
    obtain ⟨c, hc⟩ := gs_unique_W hΨ0 hL
    have hφ1 : ip (μ := μN 0) (lift φ) (lift φ) = 1 := by rw [ip_lift]; exact hφN.1.2
    refine ⟨φ, hφ, hφN.1.2, ?_⟩
    have := dens_eq_of_ae_smul (S := settingW τ 0 (fun _ => 0) continuous_const) hc h1 hφ1
    rw [← dens_lift (τ := τ) (w := fun _ => 0) (hw := continuous_const),
      dens_settingW_indep w (fun _ => 0) hw continuous_const]
    exact this.symm
  · rintro ⟨φ, hφ, h1, rfl⟩
    exact ⟨lift φ, isGS_shift.2 (isGS_lift hφ), by rw [ip_lift]; exact h1, dens_lift φ⟩

/-- **`v`-representability of one particle on `H¹₀` equals that in the `C²` box.** -/
theorem pureVRep_one_iff (ρ : C01 → ℝ) :
    PureVRep (settingW τ 0 w hw) ρ ↔ PureVRep Box.setting ρ :=
  ⟨fun ⟨v, h⟩ => ⟨_, (pureDens_one_iff v ρ).1 h⟩, fun ⟨v, h⟩ =>
    ⟨v - wPot w hw, (pureDens_one_iff _ ρ).2 (by rwa [sub_add_cancel])⟩⟩

/-- **Exact `v`-representability of one particle on `H¹₀`**, continuous `v` and `w`, pure states
or ensembles: `ρ(u) = ∫₀¹ u g²` with `g` `C²`, zero at the walls, positive inside, normalised, and
`g'' = q g` on `(0, 1)` for a continuous `q`. -/
theorem pureVRep_one_iff_boxRep (ρ : C01 → ℝ) :
    PureVRep (settingW τ 0 w hw) ρ ↔
      ∃ g q, BoxRep g q ∧ ρ = fun u => ∫ t, iccExt u t * g t ^ 2 ∂vol01 :=
  (pureVRep_one_iff ρ).trans (pureVRep_box_iff ρ)

theorem ensVRep_one_iff_boxRep (ρ : C01 → ℝ) :
    EnsVRep (settingW τ 0 w hw) ρ ↔
      ∃ g q, BoxRep g q ∧ ρ = fun u => ∫ t, iccExt u t * g t ^ 2 ∂vol01 :=
  (ensVRep_iff_W_cont ρ).trans (pureVRep_one_iff_boxRep ρ)

/-! ### Smooth counterexamples -/

/-- **A density with an interior zero is not `v`-representable** for one particle on `H¹₀`, even
if it is smooth. -/
theorem not_vrep_one_of_zero {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (hfc : f c = 0) : ¬ EnsVRep (settingW τ 0 w hw) fun u => ∫ t, iccExt u t * f t ∂vol01 := by
  intro h
  obtain ⟨g, q, ⟨hg, hpos, -, -⟩, hρ⟩ := (ensVRep_one_iff_boxRep _).1 h
  have hsq := eqOn_of_integral_pot (f := fun t => g t ^ 2) (g := f)
    (hg.1.continuous.pow 2) hf (fun u => (congrFun hρ u).symm)
  have := hsq hc
  simp only [hfc] at this
  exact (pow_pos (hpos c hc) 2).ne' this

/-- `√ρ = √2 sin(2πt)`. -/
noncomputable def sinG (t : ℝ) : ℝ := √2 * sin (2 * π * t)

/-- `ρ = 2 sin²(2πt)`: smooth and normalised, zero at `t = ½`. -/
noncomputable def sinDens (t : ℝ) : ℝ := sinG t ^ 2

lemma sinG_mem : sinG ∈ SturmLiouville.Dom := ⟨by unfold sinG; fun_prop, by simp [sinG], by simp [sinG]⟩

lemma sinG_norm : ∫ t, sinG t ^ 2 ∂vol01 = 1 := by
  rw [integral_vol01]
  have e : ∀ t, sinG t ^ 2 = 1 - cos (4 * π * t) := fun t => by
    simp only [sinG, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show 4 * π * t = 2 * (2 * π * t) by ring, cos_two_mul, cos_sq']
    ring
  simp only [e]
  have hF : ∀ t, HasDerivAt (fun t : ℝ => t - sin (4 * π * t) / (4 * π))
      (1 - cos (4 * π * t)) t := fun t => by
    have h := ((((hasDerivAt_id' t).const_mul (4 * π)).sin).div_const (4 * π))
    have := (hasDerivAt_id' t).sub h
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    ((by fun_prop : Continuous fun t : ℝ => 1 - cos (4 * π * t)).intervalIntegrable 0 1)]
  have : sin (4 * π) = 0 := by
    rw [show 4 * π = ((4 : ℕ) : ℝ) * π by push_cast; ring]
    exact sin_nat_mul_pi 4
  simp [this]

/-- **`2 sin²(2πt)` is `N`-representable but not `v`-representable** for one particle on `H¹₀`
(continuous `v` and `w`): it is the density of the normalised state `√2 sin(2πt)`, a first excited
state of the free particle, but it vanishes at `t = ½` while a ground state has no interior zero. -/
theorem sinDens_nrep_not_vrep :
    (∃ ψ ∈ Nst (settingW τ 0 w hw), dens (settingW τ 0 w hw) ψ =
        fun u => ∫ t, iccExt u t * sinDens t ∂vol01) ∧
      ¬ EnsVRep (settingW τ 0 w hw) fun u => ∫ t, iccExt u t * sinDens t ∂vol01 := by
  refine ⟨⟨lift sinG, ⟨Dom_le_DomW (lift_mem sinG_mem), ?_⟩, ?_⟩, ?_⟩
  · rw [ip_lift, ip_eq_sq, sinG_norm]
  · rw [dens_lift, dens_eq_sq]; rfl
  · refine not_vrep_one_of_zero (by unfold sinDens sinG; fun_prop)
      (by norm_num : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1) ?_
    simp only [sinDens, sinG]
    rw [show 2 * π * (1 / 2) = π by ring, sin_pi]
    simp

/-- **`30 t² (1 - t)²` is `N`-representable but not `v`-representable** for one particle on `H¹₀`
(continuous `v` and `w`): smooth and positive inside, but `g''/g = -2 / (t (1 - t))` is unbounded
at the walls. -/
theorem quartDens_nrep_not_vrep :
    (∃ ψ ∈ Nst (settingW τ 0 w hw), dens (settingW τ 0 w hw) ψ =
        fun u => ∫ t, iccExt u t * quartDens t ∂vol01) ∧
      ¬ EnsVRep (settingW τ 0 w hw) fun u => ∫ t, iccExt u t * quartDens t ∂vol01 := by
  refine ⟨⟨lift quartG, ⟨Dom_le_DomW (lift_mem quartG_mem), ?_⟩, ?_⟩, fun h => ?_⟩
  · rw [ip_lift, ip_eq_sq, quartG_norm]
  · rw [dens_lift, dens_eq_sq]; rfl
  · exact quartDens_not_vrep.2 ((pureVRep_one_iff _).1 ((ensVRep_iff_W_cont _).1 h))

end DFT.Continuum.Line
