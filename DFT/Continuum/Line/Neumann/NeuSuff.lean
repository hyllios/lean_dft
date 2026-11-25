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
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### The mass functional -/

/-- `f ↦ ∫ f` on `C([0, 1])`. -/
noncomputable def intPot : Pot →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t, ext f t ∂μ1
      map_add' := fun f g => by
        rw [← integral_add (integrable_cont_mu1 (continuous_ext f))
          (integrable_cont_mu1 (continuous_ext g))]
        rfl
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        rfl }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ t, ext f t ∂μ1‖ ≤ ‖f‖ * μ1.real univ :=
            norm_integral_le_of_norm_le_const (ae_of_all _ fun t => by
              simpa [Real.norm_eq_abs] using abs_ext_le f t)
        _ = ‖f‖ := by rw [mu1_real_univ, mul_one]

/-- The mass functional `e ↦ ∫ fnE e`, a constant potential. -/
noncomputable def ellE : PotH := intPot.comp evE

lemma ellE_apply (e : H1E) : ellE e = ∫ t, fnE e t ∂μ1 :=
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

/-! ### Sufficiency -/

/-- **`v`-representability from local `N`-representability with bounded energy.** -/
theorem vrepNH_of_rep {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {ρ0 : H1E}
    (hN : ∫ t, fnE ρ0 t ∂μ1 = n + 1)
    (hRep : ∃ r > 0, ∃ M : ℝ, ∀ h : H1E, ellE h = 0 → ‖h‖ ≤ r →
      ∃ Φ ∈ DomN τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 ∧ rhoE τ Φ = ρ0 + h ∧
        kinN Φ + ∫ x, w x * (Φ x * Φ x) ∂μN n ≤ M) :
    VRepNH τ n w ρ0 := by
  obtain ⟨r, hr, M, hM⟩ := hRep
  have hNp : (0 : ℝ) < n + 1 := by positivity
  have hellρ : ellE ρ0 = n + 1 := by rw [ellE_apply, hN]
  set G : PotH → ℝ := fun v => gsEH τ w v - v ρ0
  -- `G ≤ M + v(h)`
  have hGle : ∀ v : PotH, ∀ h : H1E, ellE h = 0 → ‖h‖ ≤ r → G v ≤ M + v h := by
    intro v h hh hhr
    obtain ⟨Φ, hΦ, hn, hρ, hE⟩ := hM h hh hhr
    have := gsEH_le (v := v) hw hΦ hn
    rw [QNH, hρ, map_add] at this
    simp only [G]; linarith
  have hGM : ∀ v, G v ≤ M := fun v => by
    simpa using hGle v 0 (map_zero _) (by rw [norm_zero]; exact hr.le)
  have hGshift : ∀ v (c : ℝ), G (v + c • ellE) = G v := fun v c => by
    simp only [G, gsEH_shift hw, add_apply, smul_apply,
      smul_eq_mul, hellρ]
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
    simp only [vs', add_apply, smul_apply, smul_eq_mul,
      hellρ]
    field_simp; ring
  -- the bound
  have hS1 : ∀ j, S - 1 ≤ G (vs' j) := fun j => by
    rw [hvs'G]
    have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith [hvs j]
  set A := M - (S - 1)
  have hA : 0 ≤ A := by
    have := hS1 0; have := hGM (vs' 0); simp only [A]; linarith
  have hX0 : ∀ j (h : H1E), ellE h = 0 → |vs' j h| ≤ A / r * ‖h‖ := by
    intro j h hh
    rcases eq_or_ne h 0 with rfl | hne
    · simp
    · have hnp : 0 < ‖h‖ := norm_pos_iff.2 hne
      set h1 := (r / ‖h‖) • h
      have hh1 : ellE h1 = 0 := by simp [h1, hh]
      have hn1 : ‖h1‖ ≤ r := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hnp.ne']
      have hn1' : ‖-h1‖ ≤ r := by rw [norm_neg]; exact hn1
      have e1 := hGle (vs' j) h1 hh1 hn1
      have e2 := hGle (vs' j) (-h1) (by simp [hh1]) hn1'
      have e3 := hS1 j
      have hv1 : vs' j h1 = r / ‖h‖ * vs' j h := by simp [h1]
      rw [map_neg, hv1] at e2
      rw [hv1] at e1
      have hb : |r / ‖h‖ * vs' j h| ≤ A := by rw [abs_le]; constructor <;> linarith
      rw [abs_mul, abs_of_pos (by positivity : 0 < r / ‖h‖)] at hb
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      calc |vs' j h| * r = r / ‖h‖ * |vs' j h| * ‖h‖ := by field_simp
        _ ≤ A * ‖h‖ := mul_le_mul_of_nonneg_right hb hnp.le
  set κ := 1 + ‖ellE‖ * ‖ρ0‖ / (n + 1)
  have hbound : ∀ j, ‖vs' j‖ ≤ A / r * κ := fun j => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
    set h0 := e - (ellE e / (n + 1)) • ρ0
    have hh0 : ellE h0 = 0 := by
      simp only [h0, map_sub, map_smul, smul_eq_mul, hellρ]; field_simp; ring
    have hve : vs' j e = vs' j h0 := by
      simp only [h0, map_sub, map_smul, smul_eq_mul, hvs'ρ, mul_zero, sub_zero]
    have hn0 : ‖h0‖ ≤ κ * ‖e‖ := by
      calc ‖h0‖ ≤ ‖e‖ + ‖(ellE e / (n + 1)) • ρ0‖ := norm_sub_le _ _
        _ = ‖e‖ + |ellE e| / (n + 1) * ‖ρ0‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hNp]
        _ ≤ ‖e‖ + ‖ellE‖ * ‖e‖ / (n + 1) * ‖ρ0‖ := by
            gcongr; rw [← Real.norm_eq_abs]; exact ellE.le_opNorm e
        _ = κ * ‖e‖ := by simp only [κ]; ring
    rw [Real.norm_eq_abs, hve]
    calc |vs' j h0| ≤ A / r * ‖h0‖ := hX0 j h0 hh0
      _ ≤ A / r * (κ * ‖e‖) := mul_le_mul_of_nonneg_left hn0 (by positivity)
      _ = A / r * κ * ‖e‖ := by ring
  -- a weak limit is a maximiser
  obtain ⟨v, φ, hφ, hlim⟩ := exists_weak_subseq_PotH hbound
  have hmax : S ≤ G v := by
    have : S + v ρ0 ≤ gsEH τ w v := by
      obtain ⟨Ψ0, hΨ0⟩ := exists_isGSNH τ hw v
      refine le_csInf ⟨_, Ψ0, hΨ0.1, hΨ0.2.1, rfl⟩ fun e ⟨Φ, hΦ, hn, he⟩ => ?_
      rw [← he]
      have hk : ∀ k, S - 1 / ((φ k : ℝ) + 1) ≤
          QNH τ w (vs' (φ k)) Φ - vs' (φ k) ρ0 := fun k => by
        have h1 := hvs (φ k)
        rw [← hvs'G] at h1
        have h2 := gsEH_le (v := vs' (φ k)) hw hΦ hn
        simp only [G] at h1
        linarith
      have hL : Tendsto (fun k => S - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 S) := by
        have := (tendsto_const_nhds (x := S)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
        simpa using this
      have hR : Tendsto (fun k => QNH τ w (vs' (φ k)) Φ - vs' (φ k) ρ0) atTop
          (𝓝 (QNH τ w v Φ - v ρ0)) := by
        simp only [QNH]
        exact ((tendsto_const_nhds.add (hlim _)).sub (hlim ρ0))
      have := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hk)
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
