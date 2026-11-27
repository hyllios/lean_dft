/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuCpt
import DFT.Continuum.Line.Neumann.NeuPos

/-!
# Sufficiency: `v`-representability from local `N`-representability

Let `ρ₀ ∈ H¹(0, 1)` with `∫ ρ₀ = N`, and suppose that every `ρ₀ + h` with `∫ h = 0` and
`‖h‖_{H¹} ≤ r` is the density of a normalised Neumann state of kinetic plus interaction energy
at most `M`. Then `ρ₀` is the ground-state density of some `v ∈ H⁻¹` (**`vrepNH_of_rep`**).

The concave function `G(v) = E(v) - v(ρ₀)` attains its maximum.

* `G ≤ M + v(h)` for every admissible `h`, so `G` is bounded above and, on potentials with
  `v(ρ₀) = 0`, coercive.
* `G` is invariant under constant shifts `v + c ∫` (`gsEH_shift`), which make `v(ρ₀) = 0`.
* A maximising sequence is then bounded in `H⁻¹` and has a weakly convergent subsequence
  (`exists_weak_subseq_PotH`). `E` is an infimum of weakly continuous affine functions, so
  `G` is weakly upper semicontinuous and the limit is a maximiser.

At a maximiser, `ρ₀` is a supergradient of `E`, hence the ground-state density
(`rhoE_eq_of_supergrad`).

The two analytic steps are stated separately, for reuse: `norm_le_of_lower` (a potential bounded
below on small mass-zero perturbations is bounded) and `le_gsEH_of_tendsto` (weak upper
semicontinuity of `E`). `LocRepNH` is the hypothesis of local `N`-representability.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### The mass functional -/

/-- `f ↦ ∫ f` on `C([0, 1])`. -/
noncomputable def intPot : C01 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t, iccExt f t ∂vol01
      map_add' := fun f g => by
        rw [← integral_add (integrable_cont_mu1 (continuous_iccExt f))
          (integrable_cont_mu1 (continuous_iccExt g))]
        rfl
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        rfl }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ t, iccExt f t ∂vol01‖ ≤ ‖f‖ * vol01.real univ :=
            norm_integral_le_of_norm_le_const (ae_of_all _ fun t => by
              simpa [Real.norm_eq_abs] using abs_ext_le f t)
        _ = ‖f‖ := by rw [mu1_real_univ, mul_one]

/-- The mass functional `e ↦ ∫ fnE e`, a constant potential. -/
noncomputable def ellE : PotH := intPot.comp evE

lemma ellE_apply (e : H1E) : ellE e = ∫ t, fnE e t ∂vol01 :=
  setIntegral_congr_fun measurableSet_Ioo fun _ ht => ext_evE (Ioo_subset_Icc_self ht)

lemma ellE_rhoE {τ : Stat} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (hn : ∫ x, Φ x ^ 2 ∂μN n = 1) :
    ellE (rhoE τ Φ) = n + 1 := by
  rw [ellE_apply, integral_fnE_rhoE hΦ, hn, mul_one]

section shift

variable {τ : Stat} {w : Cfg n → ℝ}

/-- Constant shifts of the potential shift the energy by `cN`. -/
lemma gsEH_shift (hw : Continuous w) (v : PotH) (c : ℝ) :
    gsEH τ w (v + c • ellE) = gsEH τ w v + c * (n + 1) := by
  obtain ⟨Ψ, hΨ⟩ := exists_isGSNH τ hw v
  obtain ⟨Ψ', hΨ'⟩ := exists_isGSNH τ hw (v + c • ellE)
  apply le_antisymm
  · have := gsEH_le (v := v + c • ellE) hw hΨ.1 hΨ.2.1
    rw [QNH_add_smul, ellE_rhoE hΨ.1 hΨ.2.1, ← gsEH_of_isGSNH hw hΨ] at this
    exact this
  · have h1 := gsEH_le (v := v) hw hΨ'.1 hΨ'.2.1
    have h2 := gsEH_of_isGSNH hw hΨ'
    rw [QNH_add_smul, ellE_rhoE hΨ'.1 hΨ'.2.1] at h2
    linarith

end shift

/-! ### Weak compactness of bounded sets of potentials -/

/-- **Bounded sequences in `H⁻¹` have weakly convergent subsequences.** -/
lemma exists_weak_subseq_PotH {f : ℕ → PotH} {R : ℝ} (hR : ∀ k, ‖f k‖ ≤ R) :
    ∃ g : PotH, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ e : H1E,
      Tendsto (fun k => f (φ k) e) atTop (𝓝 (g e)) := by
  set r : ℕ → H1E := fun k => (InnerProductSpace.toDual ℝ H1E).symm (f k)
  have hr : ∀ k, ‖r k‖ ≤ R := fun k => by
    simp only [r, LinearIsometryEquiv.norm_map]; exact hR k
  obtain ⟨c, -, φ₁, hφ₁, hc⟩ := tendsto_subseq_of_bounded (x := fun k => (r k).fst)
    (Metric.isBounded_Icc (-R) R) fun k => abs_le.1 ((norm_fst_le (r k)).trans (hr k))
  obtain ⟨G, φ₂, hφ₂, hw⟩ := exists_weak_subseq (f := fun k => (r (φ₁ k)).snd)
    fun k => (norm_snd_le _).trans (hr _)
  refine ⟨InnerProductSpace.toDual ℝ H1E (WithLp.toLp 2 (c, G)), φ₁ ∘ φ₂, hφ₁.comp hφ₂,
    fun e => ?_⟩
  have he : ∀ k, f k e = (r k).fst * e.fst + inner ℝ (r k).snd e.snd := fun k => by
    rw [← InnerProductSpace.toDual_symm_apply, WithLp.prod_inner_apply]
    simp only [Real.inner_apply]
    rfl
  simp only [he, Function.comp_apply, InnerProductSpace.toDual_apply_apply,
    WithLp.prod_inner_apply, Real.inner_apply]
  have h1 : Tendsto (fun k => (r (φ₁ (φ₂ k))).fst) atTop (𝓝 c) := hc.comp hφ₂.tendsto_atTop
  have := (h1.mul_const e.fst).add (hw e.snd)
  convert this using 2
  rfl

/-! ### Bounds on potentials and upper semicontinuity of `E` -/

/-- **A potential bounded below on small mass-zero perturbations is bounded.** If `v(ρ₁) = 0` for
some `ρ₁` of mass `m > 0`, and `-A ≤ v(h)` for every `h` with `∫ h = 0` and `‖h‖ ≤ r`, then
`‖v‖ ≤ A / r · (1 + ‖ℓ‖ ‖ρ₁‖ / m)`. -/
lemma norm_le_of_lower {v : PotH} {ρ1 : H1E} {m r A : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hρ1 : ellE ρ1 = m) (hv1 : v ρ1 = 0) (hA : ∀ h : H1E, ellE h = 0 → ‖h‖ ≤ r → -A ≤ v h) :
    ‖v‖ ≤ A / r * (1 + ‖ellE‖ * ‖ρ1‖ / m) := by
  have hA0 : 0 ≤ A := by simpa using hA 0 (map_zero _) (by rw [norm_zero]; exact hr.le)
  have hX0 : ∀ h : H1E, ellE h = 0 → |v h| ≤ A / r * ‖h‖ := by
    intro h hh
    rcases eq_or_ne h 0 with rfl | hne
    · simp
    · have hnp : 0 < ‖h‖ := norm_pos_iff.2 hne
      set h1 := (r / ‖h‖) • h
      have hh1 : ellE h1 = 0 := by simp [h1, hh]
      have hn1 : ‖h1‖ ≤ r := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hnp.ne']
      have e1 := hA h1 hh1 hn1
      have e2 := hA (-h1) (by simp [hh1]) (by rw [norm_neg]; exact hn1)
      have hv1 : v h1 = r / ‖h‖ * v h := by simp [h1]
      rw [map_neg, hv1] at e2
      rw [hv1] at e1
      have hb : |r / ‖h‖ * v h| ≤ A := by rw [abs_le]; constructor <;> linarith
      rw [abs_mul, abs_of_pos (by positivity : 0 < r / ‖h‖)] at hb
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      calc |v h| * r = r / ‖h‖ * |v h| * ‖h‖ := by field_simp
        _ ≤ A * ‖h‖ := mul_le_mul_of_nonneg_right hb hnp.le
  set κ := 1 + ‖ellE‖ * ‖ρ1‖ / m
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  set h0 := e - (ellE e / m) • ρ1
  have hh0 : ellE h0 = 0 := by
    simp only [h0, map_sub, map_smul, smul_eq_mul, hρ1]; field_simp; ring
  have hve : v e = v h0 := by
    simp only [h0, map_sub, map_smul, smul_eq_mul, hv1, mul_zero, sub_zero]
  have hn0 : ‖h0‖ ≤ κ * ‖e‖ := by
    calc ‖h0‖ ≤ ‖e‖ + ‖(ellE e / m) • ρ1‖ := norm_sub_le _ _
      _ = ‖e‖ + |ellE e| / m * ‖ρ1‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hm]
      _ ≤ ‖e‖ + ‖ellE‖ * ‖e‖ / m * ‖ρ1‖ := by
          gcongr; rw [← Real.norm_eq_abs]; exact ellE.le_opNorm e
      _ = κ * ‖e‖ := by simp only [κ]; ring
  rw [Real.norm_eq_abs, hve]
  calc |v h0| ≤ A / r * ‖h0‖ := hX0 h0 hh0
    _ ≤ A / r * (κ * ‖e‖) := mul_le_mul_of_nonneg_left hn0 (by positivity)
    _ = A / r * κ * ‖e‖ := by ring

/-- **`E` is weakly upper semicontinuous.** If `v_k → v` weakly, `a_k → a` and `a_k ≤ E(v_k)`,
then `a ≤ E(v)`: `E` is an infimum of weakly continuous affine functions. -/
lemma le_gsEH_of_tendsto {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {vk : ℕ → PotH}
    {v : PotH} (hlim : ∀ e : H1E, Tendsto (fun k => vk k e) atTop (𝓝 (v e))) {a : ℕ → ℝ}
    {a0 : ℝ} (ha : Tendsto a atTop (𝓝 a0)) (hle : ∀ k, a k ≤ gsEH τ w (vk k)) :
    a0 ≤ gsEH τ w v := by
  obtain ⟨Ψ0, hΨ0⟩ := exists_isGSNH τ hw v
  refine le_csInf ⟨_, Ψ0, hΨ0.1, hΨ0.2.1, rfl⟩ fun e ⟨Φ, hΦ, hn, he⟩ => ?_
  rw [← he]
  have hR : Tendsto (fun k => QNH τ w (vk k) Φ) atTop (𝓝 (QNH τ w v Φ)) := by
    simp only [QNH]
    exact tendsto_const_nhds.add (hlim _)
  exact le_of_tendsto_of_tendsto ha hR
    (Eventually.of_forall fun k => (hle k).trans (gsEH_le hw hΦ hn))

/-! ### Sufficiency -/

/-- **Local `N`-representability with bounded energy**: every `ρ₀ + h` with `∫ h = 0` and
`‖h‖ ≤ r` is the density of a normalised Neumann state with kinetic plus interaction energy at
most `M`. -/
def LocRepNH (τ : Stat) (n : ℕ) (w : Cfg n → ℝ) (ρ0 : H1E) : Prop :=
  ∃ r > 0, ∃ M : ℝ, ∀ h : H1E, ellE h = 0 → ‖h‖ ≤ r →
    ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ rhoE τ Φ = ρ0 + h ∧
      kinN Φ + ∫ x, w x * (Φ x * Φ x) ∂μN n ≤ M

/-- `G(v) = E(v) - v(ρ₀)` is at most `M + v(h)` on the admissible perturbations. -/
lemma gsEH_sub_le_of_rep {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {ρ0 h : H1E} {M : ℝ}
    {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (hn : ∫ x, Φ x ^ 2 ∂μN n = 1) (hρ : rhoE τ Φ = ρ0 + h)
    (hE : kinN Φ + ∫ x, w x * (Φ x * Φ x) ∂μN n ≤ M) (v : PotH) :
    gsEH τ w v - v ρ0 ≤ M + v h := by
  have := gsEH_le (v := v) hw hΦ hn
  rw [QNH, hρ, map_add] at this
  linarith

/-- **`v`-representability from local `N`-representability with bounded energy.** -/
theorem vrepNH_of_rep {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {ρ0 : H1E}
    (hN : ∫ t, fnE ρ0 t ∂vol01 = n + 1) (hRep : LocRepNH τ n w ρ0) : VRepNH τ n w ρ0 := by
  obtain ⟨r, hr, M, hM⟩ := hRep
  have hNp : (0 : ℝ) < n + 1 := by positivity
  have hellρ : ellE ρ0 = n + 1 := by rw [ellE_apply, hN]
  set G : PotH → ℝ := fun v => gsEH τ w v - v ρ0
  have hGle : ∀ v : PotH, ∀ h : H1E, ellE h = 0 → ‖h‖ ≤ r → G v ≤ M + v h := by
    intro v h hh hhr
    obtain ⟨Φ, hΦ, hn, hρ, hE⟩ := hM h hh hhr
    exact gsEH_sub_le_of_rep hw hΦ hn hρ hE v
  have hGM : ∀ v, G v ≤ M := fun v => by
    simpa using hGle v 0 (map_zero _) (by rw [norm_zero]; exact hr.le)
  have hGshift : ∀ v (c : ℝ), G (v + c • ellE) = G v := fun v c => by
    simp only [G, gsEH_shift hw, add_apply, smul_apply, smul_eq_mul, hellρ]
    ring
  -- a maximising sequence
  have hbdd : BddAbove (range G) := ⟨M, fun _ ⟨v, hv⟩ => hv ▸ hGM v⟩
  set S := sSup (range G)
  have hseq : ∀ j : ℕ, ∃ v, S - 1 / ((j : ℝ) + 1) < G v := fun j => by
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (range_nonempty G)
      (sub_lt_self S (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)))
    exact ⟨v, hv⟩
  choose vs hvs using hseq
  set vs' : ℕ → PotH := fun j => vs j + (-(vs j ρ0) / (n + 1)) • ellE
  have hvs'G : ∀ j, G (vs' j) = G (vs j) := fun j => hGshift _ _
  have hvs'ρ : ∀ j, vs' j ρ0 = 0 := fun j => by
    simp only [vs', add_apply, smul_apply, smul_eq_mul, hellρ]
    field_simp; ring
  have hS1 : ∀ j, S - 1 ≤ G (vs' j) := fun j => by
    rw [hvs'G]
    have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith [hvs j]
  have hbound : ∀ j, ‖vs' j‖ ≤ (M - (S - 1)) / r * (1 + ‖ellE‖ * ‖ρ0‖ / (n + 1)) := fun j =>
    norm_le_of_lower hNp hr hellρ (hvs'ρ j) fun h hh hhr => by
      linarith [hGle (vs' j) h hh hhr, hS1 j]
  -- a weak limit is a maximiser
  obtain ⟨v, φ, hφ, hlim⟩ := exists_weak_subseq_PotH hbound
  have hmax : S ≤ G v := by
    have hL : Tendsto (fun k => S - 1 / ((φ k : ℝ) + 1) + vs' (φ k) ρ0) atTop
        (𝓝 (S + v ρ0)) := by
      have := ((tendsto_const_nhds (x := S)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)).add (hlim ρ0)
      simpa using this
    have := le_gsEH_of_tendsto hw (fun e => hlim e) hL fun k => by
      have h1 := hvs (φ k)
      rw [← hvs'G] at h1
      simp only [G] at h1
      linarith
    simp only [G]; linarith
  -- `ρ₀` is a supergradient at `v`
  have hsup : ∀ v' : PotH, gsEH τ w v' ≤ gsEH τ w v + (v' - v) ρ0 := fun v' => by
    have h1 : G v' ≤ S := le_csSup hbdd ⟨v', rfl⟩
    simp only [G] at h1 hmax
    simp only [sub_apply]
    linarith
  obtain ⟨Ψ, hΨ⟩ := exists_isGSNH τ hw v
  exact ⟨v, Ψ, hΨ, rhoE_eq_of_supergrad hw hsup hΨ⟩

end DFT.Continuum.Line
