/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.Order.Star.Real
import DFT.Continuum.Box.Ground
import DFT.Continuum.Box.PiconeEq
import DFT.Continuum.General.Lieb
import DFT.Continuum.General.VRep

/-!
# `v`-representable densities of one particle in a box, exactly

For one particle on `[0, 1]` with hard walls (`C²` states, continuous potentials), a density
functional `ρ` is the density of a normalised ground state of some continuous potential iff
`ρ(v) = ∫₀¹ v g²` with
* `g` in the form domain (`C²`, zero at the walls), `g > 0` on `(0, 1)`, `∫₀¹ g² = 1`;
* `g'' / g` extending continuously to `[0, 1]`: `g'' = q g` on `(0, 1)` for a continuous `q`.

Then `g` is a ground state of `q` with energy `0` (`isGS_of_boxRep`), so `q` is the potential,
unique up to constants by Hohenberg–Kohn.

The proof:
* (⇐) Let `ψ` be the shooting ground state of `q` (`gs_data`), with energy `E*` and `ψ > 0` on
  `(0, 1)`. The Wronskian `W = g ψ' - g' ψ` vanishes at both walls and `W' = -E* g ψ`, so
  `E* ∫ g ψ = 0` and `E* = 0`. Integration by parts gives `g` energy `0 = E*`.
* (⇒) A ground state `φ` has energy `E*`, so `∫ (φ'² + (v - E*) φ²) = 0`, and the equality case
  of the Picone inequality (`picone_eq`) makes `φ` a multiple of the positive shooting solution.
  Take `g = ±φ`; `g'' = (v - E*) g`.

The condition on `g'' / g` is a genuine restriction: `quartDens = 30 t² (1 - t)²` is the density of
a normalised `C²` state with `√ρ` smooth and positive inside, but `g''/g = -2 / (t (1 - t))` is
unbounded, so it is not `v`-representable (`quartDens_not_vrep`).

* `BoxRep`: the conditions on `g`.
* `estar_eq_zero`: the Wronskian argument; `isGS_of_boxRep`.
* `pureVRep_box_iff`: **the characterisation**.
* `quartDens_not_vrep`: the example.
-/

namespace DFT.Continuum.Box

open MeasureTheory Set Filter Topology SturmLiouville

/-- The conditions on `g = √ρ` for `ρ` to be a ground-state density in the box. -/
def BoxRep (g : ℝ → ℝ) (q : Pot) : Prop :=
  g ∈ Dom ∧ (∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) ∧ ∫ t, g t ^ 2 ∂μ1 = 1 ∧
    ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv g) t = ext q t * g t

section aux

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

variable {g : ℝ → ℝ}

lemma contDiff_deriv_of_mem (hg : g ∈ Dom) : ContDiff ℝ 1 (deriv g) :=
  (contDiff_succ_iff_deriv.mp hg.1).2.2

lemma hasDerivAt_deriv_of_mem (hg : g ∈ Dom) (t : ℝ) :
    HasDerivAt (deriv g) (deriv (deriv g) t) t :=
  ((contDiff_deriv_of_mem hg).differentiable one_ne_zero t).hasDerivAt

lemma continuous_dd_of_mem (hg : g ∈ Dom) : Continuous (deriv (deriv g)) :=
  (contDiff_deriv_of_mem hg).continuous_deriv le_rfl

lemma ip_eq_sq (g : ℝ → ℝ) : ip (μ := μ1) g g = ∫ t, g t ^ 2 ∂μ1 := by
  simp only [ip, sq]

lemma dens_eq_sq (g : ℝ → ℝ) : dens setting g = fun u => ∫ t, ext u t * g t ^ 2 ∂μ1 := by
  funext u; simp only [dens, pf, sq]; rfl

lemma energy_eq_of_isGS {v : Pot} {ψ : ℝ → ℝ} (hψ : IsGS setting v ψ) (E : ℝ)
    (hQ : Q setting v ψ = E * ip (μ := μ1) ψ ψ) : energy v ψ = E := by
  rw [energy, hQ, mul_div_assoc, div_self hψ.2.1.ne', mul_one]

end aux

/-- The shooting ground state of `v` as a ground state, with energy `E* = Estar v`. -/
lemma gs_data' (v : Pot) : ∃ ψ, IsGS setting v ψ ∧ energy v ψ = Estar v ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t) ∧ ∀ φ ∈ Dom, Estar v * ip (μ := μ1) φ φ ≤ Q setting v φ := by
  obtain ⟨ψ, hD, heq, hQ, hpos, hlow⟩ := gs_data v
  have hGS : IsGS setting v ψ := ⟨hD, hpos, fun φ hφ => by
    rw [hQ]; nlinarith [mul_le_mul_of_nonneg_left (hlow φ hφ) hpos.le]⟩
  refine ⟨ψ, hGS, energy_eq_of_isGS hGS _ hQ, fun t ht => ?_, hlow⟩
  rw [heq t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  exact star_pos v t ht

/-- **The Wronskian argument**: if `g'' = q g` with `g > 0` inside and zero at the walls, the
ground-state energy of `q` is `0`. -/
theorem estar_eq_zero {g : ℝ → ℝ} {q : Pot} (hg : g ∈ Dom) (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t)
    (hode : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv g) t = ext q t * g t) : Estar q = 0 := by
  obtain ⟨ψ, hψ, hE, hψpos, -⟩ := gs_data' q
  set E := Estar q
  have hψD : ψ ∈ Dom := hψ.1
  have hψode := ode_of_isGS hψ
  rw [hE] at hψode
  set W : ℝ → ℝ := fun t => g t * deriv ψ t - deriv g t * ψ t
  set W' : ℝ → ℝ := fun t => g t * deriv (deriv ψ) t - deriv (deriv g) t * ψ t
  have hW : ∀ t, HasDerivAt W (W' t) t := fun t => by
    have h := (((diff_of_mem hg t).hasDerivAt).mul (hasDerivAt_deriv_of_mem hψD t)).sub
      ((hasDerivAt_deriv_of_mem hg t).mul ((diff_of_mem hψD t).hasDerivAt))
    convert h using 1; simp only [W']; ring
  have hW'c : Continuous W' :=
    (hg.1.continuous.mul (continuous_dd_of_mem hψD)).sub
      ((continuous_dd_of_mem hg).mul hψD.1.continuous)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hW t) (hW'c.intervalIntegrable 0 1)
  have hW0 : W 0 = 0 := by simp [W, hg.2.1, hψD.2.1]
  have hW1 : W 1 = 0 := by simp [W, hg.2.2, hψD.2.2]
  rw [hW0, hW1, sub_zero] at hftc
  have hcongr : ∫ t in (0 : ℝ)..1, W' t = ∫ t in (0 : ℝ)..1, -E * (g t * ψ t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0; simp [W', hg.2.1, hψD.2.1]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; simp [W', hg.2.2, hψD.2.2]
    simp only [W', hψode t ⟨h0, h1⟩, hode t ⟨h0, h1⟩]; ring
  rw [hcongr, intervalIntegral.integral_const_mul] at hftc
  have hI : 0 < ∫ t in (0 : ℝ)..1, g t * ψ t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hg.1.continuous.mul hψD.1.continuous).intervalIntegrable 0 1)
      (fun t ht => mul_pos (hpos t ht) (hψpos t ht)) zero_lt_one
  rcases mul_eq_zero.1 hftc with h | h
  · linarith
  · linarith

/-- **`g` is a ground state of `q`**, with energy `0`. -/
theorem isGS_of_boxRep {g : ℝ → ℝ} {q : Pot} (h : BoxRep g q) :
    IsGS setting q g ∧ Q setting q g = 0 := by
  obtain ⟨hg, hpos, hn, hode⟩ := h
  obtain ⟨-, -, -, -, hlow⟩ := gs_data' q
  rw [estar_eq_zero hg hpos hode] at hlow
  have hip : ip (μ := μ1) g g = 1 := by rw [ip_eq_sq, hn]
  -- `Q g = ∫ (g'² + q g²) = 0` by parts
  have hQ : Q setting q g = 0 := by
    have hs := Q_sub_eq q 0 hg
    rw [zero_mul, sub_zero, integral_mu1] at hs
    rw [hs]
    have hd := hasDerivAt_deriv_of_mem hg
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
      (u := deriv g) (u' := deriv (deriv g)) (v := g) (v' := deriv g)
      (fun t _ => hd t) (fun t _ => (diff_of_mem hg t).hasDerivAt)
      ((continuous_dd_of_mem hg).intervalIntegrable 0 1)
      ((cont_deriv_of_mem hg).intervalIntegrable 0 1)
    simp only [hg.2.1, hg.2.2, mul_zero, sub_zero, zero_sub] at hibp
    have hcongr : ∫ t in (0 : ℝ)..1, deriv (deriv g) t * g t =
        ∫ t in (0 : ℝ)..1, Wof q 0 t * g t ^ 2 := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0; simp [hg.2.1]
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · subst h1; simp [hg.2.2]
      simp only [hode t ⟨h0, h1⟩, Wof, sub_zero]; ring
    have hc1 := ((cont_deriv_of_mem hg).pow 2).intervalIntegrable (μ := volume) 0 1
    have hc2 := ((continuous_Wof q 0).mul (hg.1.continuous.pow 2)).intervalIntegrable
      (μ := volume) 0 1
    rw [intervalIntegral.integral_add (f := fun t => deriv g t ^ 2)
      (g := fun t => Wof q 0 t * g t ^ 2) hc1 hc2, ← hcongr]
    simp only [sq] at hibp ⊢
    linarith
  refine ⟨⟨hg, by rw [hip]; exact one_pos, fun φ hφ => ?_⟩, hQ⟩
  rw [hQ, hip, zero_mul, mul_one]
  simpa using hlow φ hφ

/-- **`v`-representability of one particle in a box, exactly.** A density functional is the
density of a normalised ground state of some continuous potential iff it is `v ↦ ∫₀¹ v g²` with
`g` `C²`, zero at the walls, positive inside, normalised, and `g'' = q g` on `(0, 1)` for a
continuous `q` (`g''/g` extends continuously to `[0, 1]`). -/
theorem pureVRep_box_iff (ρ : Pot → ℝ) :
    PureVRep setting ρ ↔ ∃ g q, BoxRep g q ∧ ρ = fun u => ∫ t, ext u t * g t ^ 2 ∂μ1 := by
  constructor
  · rintro ⟨v, φ, hφ, hφ1, rfl⟩
    obtain ⟨ψ, hψ, hE, hψpos, hlow⟩ := gs_data' v
    set E := Estar v
    have hφD : φ ∈ Dom := hφ.1
    -- `φ` has energy `E`
    have hQ : Q setting v φ = E := by
      have h1 := hlow φ hφD
      have h2 := hφ.2.2 ψ hψ.1
      have hQψ : Q setting v ψ = E * ip (μ := μ1) ψ ψ := by
        rw [← hE, energy, div_mul_cancel₀ _ hψ.2.1.ne']
      rw [hφ1] at h1 h2
      rw [hQψ] at h2
      have := hψ.2.1
      nlinarith
    have heq : ∫ x, (deriv φ x ^ 2 + Wof v E x * φ x ^ 2) ∂μ1 = 0 := by
      rw [← Q_sub_eq v E hφD, hQ, hφ1, mul_one, sub_self]
    obtain ⟨c, hc⟩ := picone_eq (continuous_Wof v E) (ψ := fun t => (sol v E t).1)
      (ψ' := fun t => (sol v E t).2)
      (fun t ht => hasDerivAt_fst_of (sol_deriv v E) ht)
      (fun t ht => hasDerivAt_snd_of (sol_deriv v E) ht)
      (star_pos v) (by simp [sol_zero]) (star_one v) (by simp [sol_zero]) (star_d1 v) hφD heq
    -- `c ≠ 0`
    have hc0 : c ≠ 0 := by
      rintro rfl
      have : ip (μ := μ1) φ φ = 0 := by
        simp only [ip]
        rw [show (0 : ℝ) = ∫ x in Ioo (0 : ℝ) 1, (0 : ℝ) by simp]
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        simp [hc x hx]
      rw [hφ1] at this; exact one_ne_zero this
    set s : ℝ := if 0 < c then 1 else -1
    have hs2 : s * s = 1 := by simp only [s]; split_ifs <;> norm_num
    have hsc : 0 < s * c := by
      simp only [s]; split_ifs with h
      · linarith
      · have : c < 0 := lt_of_le_of_ne (not_lt.1 h) hc0
        linarith
    set g : ℝ → ℝ := fun t => s * φ t
    have hgD : g ∈ Dom := Dom.smul_mem s hφD
    have hdg : deriv g = fun t => s * deriv φ t := funext fun t =>
      deriv_const_mul s (diff_of_mem hφD t)
    have hddg : deriv (deriv g) = fun t => s * deriv (deriv φ) t := by
      rw [hdg]; exact funext fun t =>
        deriv_const_mul s ((contDiff_deriv_of_mem hφD).differentiable one_ne_zero t)
    have hφode := ode_of_isGS hφ
    set q : Pot := v - ContinuousMap.const _ (energy v φ)
    have hq : ∀ t, ext q t = ext v t - energy v φ := fun t => rfl
    refine ⟨g, q, ⟨hgD, fun t ht => ?_, ?_, fun t ht => ?_⟩, ?_⟩
    · simp only [g, hc t ht]
      rw [← mul_assoc]; exact mul_pos hsc (star_pos v t ht)
    · simp only [g, mul_pow, sq s, hs2, one_mul]
      rw [← ip_eq_sq, hφ1]
    · rw [hddg]; change s * deriv (deriv φ) t = _; rw [hφode t ht, hq]; simp only [g]; ring
    · rw [dens_eq_sq]
      funext u
      simp only [g, mul_pow, sq s, hs2, one_mul]
  · rintro ⟨g, q, h, rfl⟩
    obtain ⟨hGS, -⟩ := isGS_of_boxRep h
    exact ⟨q, g, hGS, by rw [ip_eq_sq, h.2.2.1], dens_eq_sq g⟩

/-! ### A smooth, positive density that is not `v`-representable -/

/-- `√ρ = √30 t (1 - t)`. -/
noncomputable def quartG (t : ℝ) : ℝ := √30 * (t * (1 - t))

/-- `ρ = 30 t² (1 - t)²`: smooth, positive inside and normalised, but it would need the potential
`-2 / (t (1 - t))`, unbounded at the walls. -/
noncomputable def quartDens (t : ℝ) : ℝ := quartG t ^ 2

lemma quartG_mem : quartG ∈ Dom := ⟨by unfold quartG; fun_prop, by simp [quartG], by simp [quartG]⟩

lemma quartG_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < quartG t :=
  mul_pos (Real.sqrt_pos.2 (by norm_num)) (mul_pos ht.1 (by linarith [ht.2]))

lemma quartG_norm : ∫ t, quartG t ^ 2 ∂μ1 = 1 := by
  rw [integral_mu1]
  have e : ∀ t, quartG t ^ 2 = 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4 := fun t => by
    simp only [quartG, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]; ring
  simp only [e]
  have hF : ∀ t, HasDerivAt (fun t : ℝ => 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5)
      (30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4) t := fun t => by
    have := (((hasDerivAt_pow 3 t).const_mul 10).sub ((hasDerivAt_pow 4 t).const_mul 15)).add
      ((hasDerivAt_pow 5 t).const_mul 6)
    convert this using 1; push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    ((by fun_prop : Continuous fun t : ℝ => 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4).intervalIntegrable
      0 1)]
  norm_num

lemma dd_quartG (t : ℝ) : deriv (deriv quartG) t = -2 * √30 := by
  have h1 : ∀ s, HasDerivAt quartG (√30 * (1 - 2 * s)) s := fun s => by
    have : HasDerivAt (fun y : ℝ => √30 * (y * (1 - y))) (√30 * (1 * (1 - s) + s * -1)) s :=
      ((hasDerivAt_id' s).mul ((hasDerivAt_id' s).const_sub 1)).const_mul √30
    exact this.congr_deriv (by ring)
  have hd : deriv quartG = fun s => √30 * (1 - 2 * s) := funext fun s => (h1 s).deriv
  rw [hd]
  have : HasDerivAt (fun y : ℝ => √30 * (1 - 2 * y)) (√30 * -(2 * 1)) t :=
    (((hasDerivAt_id' t).const_mul 2).const_sub 1).const_mul √30
  rw [this.deriv]; ring

/-- **`30 t² (1 - t)²` is `N`-representable but not `v`-representable.** It is the density of the
normalised `C²` state `√30 t (1 - t)`, positive inside, but `g''/g = -2 / (t (1 - t))` is unbounded
at the walls, so no continuous potential has it as a ground-state density. -/
theorem quartDens_not_vrep :
    (∃ ψ ∈ Nst setting, dens setting ψ = fun u => ∫ t, ext u t * quartDens t ∂μ1) ∧
      ¬ PureVRep setting fun u => ∫ t, ext u t * quartDens t ∂μ1 := by
  refine ⟨⟨quartG, ⟨quartG_mem, by rw [ip_eq_sq, quartG_norm]⟩, dens_eq_sq _⟩, fun h => ?_⟩
  obtain ⟨g, q, ⟨hg, hpos, -, hode⟩, hρ⟩ := (pureVRep_box_iff _).1 h
  -- `g = quartG` on `(0, 1)`
  have hsq := eqOn_of_integral_pot (f := fun t => g t ^ 2) (g := quartDens)
    (hg.1.continuous.pow 2) (by unfold quartDens quartG; fun_prop)
    (fun u => (congrFun hρ u).symm)
  have hgq : EqOn g quartG (Ioo 0 1) := fun t ht =>
    (pow_left_inj₀ (hpos t ht).le (quartG_pos ht).le two_ne_zero).1 (hsq ht)
  have hdd : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv g) t = -2 * √30 := fun t ht => by
    have hev : g =ᶠ[𝓝 t] quartG := eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) hgq
    rw [hev.deriv.deriv_eq, dd_quartG]
  -- `|q| ≤ M`, but `q t · t (1 - t) = -2`
  set M := ‖q‖
  have hM : 0 ≤ M := norm_nonneg _
  set t : ℝ := 1 / (M + 2)
  have ht0 : 0 < t := by positivity
  have htM : M * t < 1 := by
    simp only [t]; rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have ht1 : t < 1 := by simp only [t]; rw [div_lt_one (by linarith)]; linarith
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have key := hode t ht
  rw [hdd t ht, hgq ht, quartG] at key
  have h30 : 0 < √30 := Real.sqrt_pos.2 (by norm_num)
  have hq : ext q t * (t * (1 - t)) = -2 := by
    have : √30 * (ext q t * (t * (1 - t)) + 2) = 0 := by linear_combination -key
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hb := abs_ext_le q t
  have hp : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have : |ext q t| * (t * (1 - t)) = 2 := by
    rw [← abs_of_pos hp, ← abs_mul, hq]; norm_num
  nlinarith [mul_le_mul_of_nonneg_right hb hp.le, mul_le_mul_of_nonneg_left
    (show t * (1 - t) ≤ t by nlinarith) hM]

end DFT.Continuum.Box
