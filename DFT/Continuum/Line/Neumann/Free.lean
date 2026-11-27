/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Core.Pauli
import DFT.Continuum.Line.Neumann.Spec

/-!
# Non-interacting ground states with Neumann walls

For `v ∈ H⁻¹` and no interaction, the ground-state energy of `N` fermions is the sum of the `N`
lowest Neumann eigenvalues of `-d²/dx² + v`, and that of `N` bosons is `N λ₀`.

## Slices of a smooth state

For a `C²` state `X`, the slice along coordinate `0` at `y ∈ ℝⁿ` is `s_y(t) = X(t, y)`. As an
element of `H1E` it depends continuously on `y` (`continuous_sE`), and:

* `kinN X = N ∫_y ‖s_y'‖²` (`kinN_eq_slices`, by symmetry),
* `ρ_X = N ∫_y s_y²` as a Bochner integral in `H1E` (`rhoE_eq_slices`), so
  `v(ρ_X) = N ∫_y v(s_y²)` for every `v ∈ H⁻¹`,
* `∫ X² = ∫_y ‖s_y‖²`, and `∫_y ⟪g, s_y⟫² = ⟨X, P₀ X⟩` is the occupation of the orbital `g`
  by particle `0`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

variable {n : ℕ}

/-! ### From continuous functions to `L²(0, 1)` -/

/-- `C([0, 1]) → L²(0, 1)`. -/
noncomputable def jC : C01 →L[ℝ] HL :=
  Jop.comp (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) 1) ℝ ℝ).toLinearIsometry.toContinuousLinearMap

lemma jC_ae (f : C01) : (jC f : ℝ → ℝ) =ᵐ[vol01] iccExt f := by
  filter_upwards [MemLp.coeFn_toLp (memLp_comp_projIcc
    ((ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) 1) ℝ ℝ) f))] with x hx
  change (Jop _ : ℝ → ℝ) x = _
  simp only [Jop, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
  exact hx.trans rfl

/-! ### Slices -/

/-- The slices `y ↦ (t ↦ F(t, y))` of a continuous function, as a continuous map into
`C([0, 1])`. -/
noncomputable def insC (F : Cfg n → ℝ) (hF : Continuous F) : C(Fin n → ℝ, C01) :=
  ContinuousMap.curry ⟨fun p : (Fin n → ℝ) × Icc (0 : ℝ) 1 => F (Fin.insertNth 0 (p.2 : ℝ) p.1),
    hF.comp (Continuous.finInsertNth 0 (continuous_subtype_val.comp continuous_snd) continuous_fst)⟩

lemma insC_apply (F : Cfg n → ℝ) (hF : Continuous F) (y : Fin n → ℝ) (t : Icc (0 : ℝ) 1) :
    insC F hF y t = F (Fin.insertNth 0 (t : ℝ) y) := rfl

lemma iccExt_insC (F : Cfg n → ℝ) (hF : Continuous F) (y : Fin n → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : iccExt (insC F hF y) t = F (Fin.insertNth 0 t y) := by
  simp [iccExt, insC_apply, projIcc_of_mem _ ht]

variable {τ : Stat} {X : Cfg n → ℝ}

lemma contDiff_slice (hX : X ∈ DomC τ n) (y : Fin n → ℝ) :
    ContDiff ℝ 1 fun t => X (Fin.insertNth 0 t y) :=
  (hX.1.comp (contDiff_insertNth 0 y)).of_le (by norm_num)

/-- **The slice** `s_y(t) = X(t, y)` as an element of `H1E`. -/
noncomputable def sE (hX : X ∈ DomC τ n) (y : Fin n → ℝ) : H1E :=
  toE (h1N_of_C1 (contDiff_slice hX y))

lemma fnE_sE (hX : X ∈ DomC τ n) (y : Fin n → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (sE hX y) t = X (Fin.insertNth 0 t y) := fnE_toE _ ht

lemma sE_snd_ae (hX : X ∈ DomC τ n) (y : Fin n → ℝ) :
    ((sE hX y).snd : ℝ → ℝ) =ᵐ[vol01] fun t => dk 0 X (Fin.insertNth 0 t y) := by
  filter_upwards [dN_ae (h1N_of_C1 (contDiff_slice hX y))] with t ht
  simp only [sE, toE, WithLp.toLp_snd]
  rw [ht, (hasDerivAt_insertNth (diffC hX) 0 y t).deriv]

lemma sE_eq (hX : X ∈ DomC τ n) (y : Fin n → ℝ) :
    sE hX y = WithLp.toLp 2 (X (Fin.insertNth 0 0 y),
      jC (insC (dk 0 X) (cont_dkC hX 0) y)) := by
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · simp [sE, toE]
  · simp only [WithLp.ofLp_toLp]
    refine Lp.ext ?_
    filter_upwards [sE_snd_ae hX y, jC_ae (insC (dk 0 X) (cont_dkC hX 0) y),
      ae_restrict_mem measurableSet_Ioo] with t h1 h2 ht
    change ((sE hX y).snd : ℝ → ℝ) t = _
    rw [h1, h2, iccExt_insC _ _ _ (Ioo_subset_Icc_self ht)]

/-- **Slices depend continuously on `y`.** -/
lemma continuous_sE (hX : X ∈ DomC τ n) : Continuous (sE hX) := by
  have h : sE hX = fun y => WithLp.toLp 2 (X (Fin.insertNth 0 0 y),
      jC (insC (dk 0 X) (cont_dkC hX 0) y)) := funext (sE_eq hX)
  rw [h]
  refine (WithLp.prod_continuous_toLp 2 ℝ HL).comp (Continuous.prodMk ?_ ?_)
  · exact hX.1.continuous.comp (Continuous.finInsertNth 0 continuous_const continuous_id)
  · exact jC.continuous.comp (insC (dk 0 X) (cont_dkC hX 0)).continuous

/-! ### Slice identities -/

lemma integrableOn_cube'_of_continuous {E : Type*} [NormedAddCommGroup E] {g : (Fin n → ℝ) → E}
    (hg : Continuous g) : IntegrableOn g (Cube' n) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (pi_mono fun _ _ => Ioo_subset_Icc_self)

lemma norm_JE_sE (hX : X ∈ DomC τ n) (y : Fin n → ℝ) :
    ‖JE (sE hX y)‖ ^ 2 = ∫ t, X (Fin.insertNth 0 t y) ^ 2 ∂vol01 := by
  rw [norm_JE_sq]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    simp only [fnE_sE hX y (Ioo_subset_Icc_self ht)]

lemma inner_JE_sE (hX : X ∈ DomC τ n) (e : H1E) (y : Fin n → ℝ) :
    ⟪JE e, JE (sE hX y)⟫_ℝ = ∫ t, iccExt (evE e) t * X (Fin.insertNth 0 t y) ∂vol01 := by
  rw [inner_JE]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    simp only [fnE_sE hX y (Ioo_subset_Icc_self ht), ext_evE (Ioo_subset_Icc_self ht)]

lemma norm_snd_sE (hX : X ∈ DomC τ n) (y : Fin n → ℝ) :
    ‖(sE hX y).snd‖ ^ 2 = ∫ t, dk 0 X (Fin.insertNth 0 t y) ^ 2 ∂vol01 := by
  rw [norm_sq_L2I]
  refine integral_congr_ae ?_
  filter_upwards [sE_snd_ae hX y] with t ht
  rw [ht]

/-- Under a transposition `σ = (0 k)`, the derivative along `k` becomes the one along `0`. -/
lemma dk_pm_swap (hX : X ∈ DomC τ n) (k : Fin (n + 1)) (x : Cfg n) :
    dk k X (pm (Equiv.swap 0 k) x) = ch τ (Equiv.swap 0 k) * dk 0 X x := by
  set σ := Equiv.swap (0 : Fin (n + 1)) k
  have h1 := dk_comp_pm (diffC hX) σ 0 x
  have h2 : (fun y => X (pm σ y)) = ch τ σ • X := funext fun y => by
    rw [Pi.smul_apply, smul_eq_mul]; exact hX.2 σ y
  rw [h2, dk_smul (diffC hX), Pi.smul_apply, smul_eq_mul] at h1
  have hσ : σ⁻¹ 0 = k := by simp [σ, Equiv.swap_inv]
  rw [hσ] at h1
  exact h1.symm

lemma integral_dk_sq_eq (hX : X ∈ DomC τ n) (k : Fin (n + 1)) :
    ∫ x, dk k X x * dk k X x ∂μN n = ∫ x, dk 0 X x * dk 0 X x ∂μN n := by
  rw [← integral_pm (Equiv.swap 0 k) (fun x => dk k X x * dk k X x)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [dk_pm_swap hX k x]
  linear_combination (dk 0 X x * dk 0 X x) * ch_mul_self τ (Equiv.swap 0 k)

/-- **Kinetic energy through slices**: `kinN X = N ∫_y ‖s_y'‖²`. -/
theorem kinN_eq_slices (hX : X ∈ DomC τ n) :
    kinN X = (n + 1) * ∫ y in Cube' n, ‖(sE hX y).snd‖ ^ 2 := by
  have hd : ∀ k, Continuous (dk k X) := cont_dkC hX
  have hk : ∀ k, ∫ x, dWN k X x * dWN k X x ∂μN n = ∫ x, dk 0 X x * dk 0 X x ∂μN n := by
    intro k
    rw [← integral_dk_sq_eq hX k]
    refine integral_congr_ae ?_
    filter_upwards [dWN_ae_eq (isWDN_of_C1 (hX.1.of_le (by norm_num)) k)] with x hx
    rw [hx]
  simp only [kinN, hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  congr 1
  rw [integral_cube_ins 0 (F := fun x => dk 0 X x * dk 0 X x) (integrableN ((hd 0).mul (hd 0)))]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => ?_
  rw [norm_snd_sE]
  simp only [sq]

/-- `∫ X² = ∫_y ‖s_y‖²`. -/
theorem integral_sq_eq_slices (hX : X ∈ DomC τ n) :
    ∫ x, X x * X x ∂μN n = ∫ y in Cube' n, ‖JE (sE hX y)‖ ^ 2 := by
  have hc := hX.1.continuous
  rw [integral_cube_ins 0 (F := fun x => X x * X x) (integrableN (hc.mul hc))]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => ?_
  rw [norm_JE_sE]
  simp only [sq]

/-! ### The density through slices -/

/-- The product `(e, h) ↦ e h` on `H1E` as a continuous bilinear map. -/
noncomputable def mulE : H1E →L[ℝ] H1E →L[ℝ] H1E :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ dE2 dE2_add_left (fun c e h => dE2_smul_left c e h) dE2_add_right
      (fun c e h => dE2_smul_right c e h))
    (1 + 2 * ‖evE‖) fun e h => by simpa using norm_dE2_le e h

lemma continuous_dE : Continuous dE := by
  have : dE = fun e => mulE e e := funext fun e => (dE2_self e).symm
  rw [this]
  exact mulE.continuous₂.comp (continuous_id.prodMk continuous_id)

lemma fnE_dE (e : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : fnE (dE e) t = fnE e t * fnE e t := by
  rw [dE_eq_sqE, sqE, fnE_toE _ ht]

/-- `e ↦ ∫ u · e` on `H1E`, for `u ∈ C([0, 1])`. -/
noncomputable def intU (u : C01) : H1E →L[ℝ] ℝ := (innerSL ℝ (jC u)).comp (jC.comp evE)

lemma intU_apply (u : C01) (e : H1E) :
    intU u e = ∫ t, iccExt u t * iccExt (evE e) t ∂vol01 := by
  simp only [intU, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [jC_ae u, jC_ae (evE e)] with t h1 h2
  simp [h1, h2, mul_comm]

lemma integrableOn_dE_sE (hX : X ∈ DomC τ n) :
    Integrable (fun y => dE (sE hX y)) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (continuous_dE.comp (continuous_sE hX))

/-- Each coordinate carries the same share of `∫ u(x_k) X²` (symmetry). -/
lemma integral_coord_sq (hX : X ∈ DomC τ n) (u : C01) (k : Fin (n + 1)) :
    ∫ x, iccExt u (x k) * (X x * X x) ∂μN n = ∫ x, iccExt u (x 0) * (X x * X x) ∂μN n := by
  rw [← integral_pm (Equiv.swap 0 k) (fun x => iccExt u (x k) * (X x * X x))]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [pm_apply, Equiv.swap_apply_right, hX.2]
  linear_combination (iccExt u (x 0) * (X x * X x)) * ch_mul_self τ (Equiv.swap 0 k)

/-- **The density through slices**: `ρ_X = N ∫_y s_y²` in `H1E`. -/
theorem rhoE_eq_slices (hX : X ∈ DomC τ n) (hXN : X ∈ DomN τ n) :
    rhoE τ X = ((n : ℝ) + 1) • ∫ y in Cube' n, dE (sE hX y) := by
  have hc := hX.1.continuous
  refine eq_of_int fun u => ?_
  rw [← intU_apply, ← intU_apply, map_smul, ← (intU u).integral_comp_comm (integrableOn_dE_sE hX),
    intU_apply, int_rhoE hXN, pfN, smul_eq_mul]
  have hu := continuous_iccExt u
  have hint : ∀ k : Fin (n + 1), Integrable (fun x => iccExt u (x k) * (X x * X x)) (μN n) :=
    fun k => integrableN ((hu.comp (continuous_apply k)).mul (hc.mul hc))
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => hint k]
  simp only [integral_coord_sq hX u, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  congr 1
  rw [integral_cube_ins 0 (F := fun x => iccExt u (x 0) * (X x * X x)) (hint 0)]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => ?_
  rw [intU_apply]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have htI := Ioo_subset_Icc_self ht
  simp only [Fin.insertNth_apply_same, ext_evE htI, fnE_dE _ htI, fnE_sE hX y htI]

/-- **The potential energy through slices**: `v(ρ_X) = N ∫_y v(s_y²)`. -/
theorem v_rhoE_eq_slices (hX : X ∈ DomC τ n) (hXN : X ∈ DomN τ n) (v : PotH) :
    v (rhoE τ X) = ((n : ℝ) + 1) * ∫ y in Cube' n, v (dE (sE hX y)) := by
  rw [rhoE_eq_slices hX hXN, map_smul, v.integral_comp_comm (integrableOn_dE_sE hX), smul_eq_mul]

/-! ### Occupations -/

section occupation

variable {X : Cfg n → ℝ} (hX : X ∈ DomC .fer n) {g : ℝ → ℝ} (hg : Continuous g)

lemma anti_of_domC (hX : X ∈ DomC .fer n) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    X (pm σ x) = sgn σ * X x := by rw [hX.2 σ x, ch_fer]

include hX hg

/-- The occupation of `g` by particle `0` through slices: `⟨X, P₀ X⟩ = ∫_y ⟪g, s_y⟫²`. -/
lemma inner_pK_zero_eq :
    ∫ x, X x * pK X g 0 x ∂μN n =
      ∫ y in Cube' n, (∫ t, g t * X (Fin.insertNth 0 t y) ∂vol01) ^ 2 := by
  have hc := hX.1.continuous
  rw [inner_pK hc (anti_of_domC hX) hg 0]
  have hG := continuous_gK hc (anti_of_domC hX) hg 0
  rw [integral_cube_ins 0 (F := fun x => gK X g 0 x * gK X g 0 x) (integrableN (hG.mul hG))]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => ?_
  have e : ∀ t, gK X g 0 (Fin.insertNth 0 t y) = ∫ s, g s * X (Fin.insertNth 0 s y) ∂vol01 :=
    fun t => by simp only [gK_apply, Fin.update_insertNth]
  simp only [e]
  change ∫ _, _ ∂vol01 = _
  rw [integral_const, mu1_real_univ, one_smul, sq]

/-- Every particle has the same occupation (antisymmetry). -/
lemma inner_pK_eq_zero (k : Fin (n + 1)) :
    ∫ x, X x * pK X g k x ∂μN n = ∫ x, X x * pK X g 0 x ∂μN n := by
  have hc := hX.1.continuous
  rw [inner_pK hc (anti_of_domC hX) hg k, inner_pK hc (anti_of_domC hX) hg 0,
    ← integral_pm (Equiv.swap 0 k) (fun x => gK X g 0 x * gK X g 0 x)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  set σ := Equiv.swap (0 : Fin (n + 1)) k
  have hupd : ∀ t, Function.update (pm σ x) 0 t = pm σ (Function.update x k t) := fun t => by
    funext i
    simp only [pm_apply, Function.update_apply]
    by_cases hi : i = 0
    · subst hi; simp [σ]
    · have : σ i ≠ k := by
        intro h; apply hi
        have := congrArg σ.symm h
        simpa [σ, Equiv.swap_apply_right] using this
      simp [hi, this]
  have hg0 : gK X g 0 (pm σ x) = sgn σ * gK X g k x := by
    simp only [gK_apply, hupd, anti_of_domC hX, ← integral_const_mul]
    congr 1; funext t; ring
  simp only [hg0]
  have h1 : (sgn σ : ℝ) * sgn σ = 1 := by
    have := ch_mul_self Stat.fer σ; simpa using this
  linear_combination (-(gK X g k x * gK X g k x)) * h1

/-- **Pauli through slices**: `N ∫_y ⟪g, s_y⟫² ≤ ∫ X²` for a normalised orbital `g`. -/
lemma occ_le (hg1 : ∫ t, g t * g t ∂vol01 = 1) :
    ((n : ℝ) + 1) * ∫ y in Cube' n, (∫ t, g t * X (Fin.insertNth 0 t y) ∂vol01) ^ 2 ≤
      ∫ x, X x * X x ∂μN n := by
  have h := pauli hX.1.continuous (anti_of_domC hX) hg hg1
  simp only [inner_pK_eq_zero hX hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, inner_pK_zero_eq hX hg] at h
  push_cast at h
  exact h

end occupation

/-! ### Lower bounds for smooth states -/

section lower

variable (v : PotH) {φ : ℕ → H1E} {lam : ℕ → ℝ} {b : HilbertBasis ℕ ℝ HL}
  (hJ : ∀ k, JE (φ k) = b k)
  (hbd : ∀ (N : ℕ) (ψ : H1E), ∑ j ∈ Finset.range N, lam j * ⟪b j, JE ψ⟫_ℝ ^ 2 +
    lam N * (‖JE ψ‖ ^ 2 - ∑ j ∈ Finset.range N, ⟪b j, JE ψ⟫_ℝ ^ 2) ≤ ‖ψ.snd‖ ^ 2 + v (dE ψ))

lemma continuous_snd_sE (hX : X ∈ DomC τ n) : Continuous fun y => (sE hX y).snd :=
  continuous_snd.comp ((WithLp.prod_continuous_ofLp 2 ℝ HL).comp (continuous_sE hX))

lemma int_snd_sq (hX : X ∈ DomC τ n) :
    Integrable (fun y => ‖(sE hX y).snd‖ ^ 2) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (g := fun y => ‖(sE hX y).snd‖ ^ 2)
    ((continuous_snd_sE hX).norm.pow 2)

lemma int_v_dE (hX : X ∈ DomC τ n) :
    Integrable (fun y => v (dE (sE hX y))) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (g := fun y => v (dE (sE hX y)))
    (v.continuous.comp (continuous_dE.comp (continuous_sE hX)))

lemma int_JE_sq (hX : X ∈ DomC τ n) :
    Integrable (fun y => ‖JE (sE hX y)‖ ^ 2) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (g := fun y => ‖JE (sE hX y)‖ ^ 2)
    ((JE.continuous.comp (continuous_sE hX)).norm.pow 2)

/-- The slice energy `‖s_y'‖² + v(s_y²)` integrates to the energy over `N`. -/
lemma integral_slice_energy (hX : X ∈ DomC τ n) (hXN : X ∈ DomN τ n) :
    ((n : ℝ) + 1) * ∫ y in Cube' n, (‖(sE hX y).snd‖ ^ 2 + v (dE (sE hX y))) =
      kinN X + v (rhoE τ X) := by
  rw [integral_add (int_snd_sq hX) (int_v_dE v hX), mul_add, kinN_eq_slices hX,
    v_rhoE_eq_slices hX hXN]

include hJ in
lemma norm_orbital (hb1 : ∀ k, ‖b k‖ = 1) (k : ℕ) :
    ∫ t, iccExt (evE (φ k)) t * iccExt (evE (φ k)) t ∂vol01 = 1 := by
  have h := norm_JE_sq (φ k)
  rw [hJ, hb1, one_pow] at h
  refine (setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_).trans h.symm
  simp only [ext_evE (Ioo_subset_Icc_self ht), sq]

include hJ hbd in
/-- **Lower bound for smooth fermionic states**: `Σ_{j ≤ n} λ_j ∫ X² ≤ T(X) + v(ρ_X)`. -/
theorem lower_smooth_fer (hmono : Monotone lam) {X : Cfg n → ℝ} (hX : X ∈ DomC .fer n)
    (hXN : X ∈ DomN .fer n) :
    (∑ j ∈ Finset.range (n + 1), lam j) * ∫ x, X x * X x ∂μN n ≤ kinN X + v (rhoE .fer X) := by
  set Λ := lam (n + 1)
  set c : ℕ → (Fin n → ℝ) → ℝ := fun j y => ⟪b j, JE (sE hX y)⟫_ℝ
  have hc : ∀ j, Continuous (c j) := fun j =>
    continuous_const.inner (JE.continuous.comp (continuous_sE hX))
  have hJs : Continuous fun y => ‖JE (sE hX y)‖ ^ 2 :=
    (JE.continuous.comp (continuous_sE hX)).norm.pow 2
  -- the one-particle bound on each slice, rearranged
  have hpt : ∀ y, ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * c j y ^ 2 + Λ * ‖JE (sE hX y)‖ ^ 2 ≤
      ‖(sE hX y).snd‖ ^ 2 + v (dE (sE hX y)) := fun y => by
    have h := hbd (n + 1) (sE hX y)
    have e : ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * c j y ^ 2 + Λ * ‖JE (sE hX y)‖ ^ 2 =
        ∑ j ∈ Finset.range (n + 1), lam j * c j y ^ 2 +
          Λ * (‖JE (sE hX y)‖ ^ 2 - ∑ j ∈ Finset.range (n + 1), c j y ^ 2) := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
    rw [e]; exact h
  have hLi : ∀ j, Integrable (fun y => (lam j - Λ) * c j y ^ 2) (volume.restrict (Cube' n)) :=
    fun j => integrableOn_cube'_of_continuous (g := fun y => (lam j - Λ) * c j y ^ 2)
      (continuous_const.mul ((hc j).pow 2))
  have hS : Integrable (fun y => ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * c j y ^ 2)
      (volume.restrict (Cube' n)) := integrable_finsetSum _ fun j _ => hLi j
  have hint := integral_mono (hS.add ((int_JE_sq hX).const_mul Λ))
    ((int_snd_sq hX).add (int_v_dE v hX)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add hS ((int_JE_sq hX).const_mul Λ), integral_finsetSum _ fun j _ => hLi j,
    integral_const_mul] at hint
  simp only [integral_const_mul] at hint
  rw [← integral_sq_eq_slices hX] at hint
  have hE := integral_slice_energy v hX hXN
  -- occupations
  have hocc : ∀ j, ((n : ℝ) + 1) * ∫ y in Cube' n, c j y ^ 2 ≤ ∫ x, X x * X x ∂μN n := fun j => by
    have e : ∀ y, c j y = ∫ t, iccExt (evE (φ j)) t * X (Fin.insertNth 0 t y) ∂vol01 :=
      fun y => by simp only [c, ← hJ j, inner_JE_sE]
    simp only [e]
    exact occ_le hX (continuous_iccExt _) (norm_orbital hJ (fun k => b.orthonormal.1 k) j)
  have hterm : ∀ j ∈ Finset.range (n + 1), (lam j - Λ) * ∫ x, X x * X x ∂μN n ≤
      (lam j - Λ) * (((n : ℝ) + 1) * ∫ y in Cube' n, c j y ^ 2) := fun j hj =>
    mul_le_mul_of_nonpos_left (hocc j)
      (sub_nonpos.2 (hmono (by simp at hj; omega)))
  have hsum := Finset.sum_le_sum hterm
  simp only [← Finset.sum_mul] at hsum
  have hN : ((n : ℝ) + 1) * ((∑ j ∈ Finset.range (n + 1), (lam j - Λ) * ∫ y in Cube' n, c j y ^ 2) +
      Λ * ∫ x, X x * X x ∂μN n) ≤ kinN X + v (rhoE .fer X) := by
    rw [← hE]; exact mul_le_mul_of_nonneg_left hint (by positivity)
  have hexp : ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * ∫ y in Cube' n, c j y ^ 2 =
      ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * (((n : ℝ) + 1) * ∫ y in Cube' n, c j y ^ 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hΛ : ∑ j ∈ Finset.range (n + 1), (lam j - Λ) =
      ∑ j ∈ Finset.range (n + 1), lam j - ((n : ℝ) + 1) * Λ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  rw [hΛ] at hsum
  nlinarith [hsum, hN, hexp]

include hbd in
/-- **Lower bound for smooth bosonic states**: `N λ₀ ∫ X² ≤ T(X) + v(ρ_X)`. -/
theorem lower_smooth_bos {X : Cfg n → ℝ} (hX : X ∈ DomC .bos n) (hXN : X ∈ DomN .bos n) :
    ((n : ℝ) + 1) * lam 0 * ∫ x, X x * X x ∂μN n ≤ kinN X + v (rhoE .bos X) := by
  have hJs : Continuous fun y => ‖JE (sE hX y)‖ ^ 2 :=
    (JE.continuous.comp (continuous_sE hX)).norm.pow 2
  have hpt : ∀ y, lam 0 * ‖JE (sE hX y)‖ ^ 2 ≤ ‖(sE hX y).snd‖ ^ 2 + v (dE (sE hX y)) :=
    fun y => by simpa using hbd 0 (sE hX y)
  have hint := integral_mono ((int_JE_sq hX).const_mul (lam 0))
    ((int_snd_sq hX).add (int_v_dE v hX)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_const_mul, ← integral_sq_eq_slices hX] at hint
  rw [← integral_slice_energy v hX hXN, mul_assoc]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

end lower

end DFT.Continuum.Line
