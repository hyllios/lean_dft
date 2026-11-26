/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import QM.Finite.Adiabatic

/-!
# Smooth eigenprojections

For a self-adjoint operator `T` on a finite-dimensional complex Hilbert space with an orthonormal
eigenbasis `e_k` and eigenvalues `λ_k`, the resolvent is `(z - T)⁻¹ = Σ_k (z - λ_k)⁻¹ |e_k⟩⟨e_k|`.
Integrating over a circle that encloses the eigenvalue `E` and no other eigenvalue gives the
**Riesz formula** `(2πi)⁻¹ ∮ (z - T)⁻¹ dz = P`, the orthogonal projection onto `ker (T - E)`.

For a `C²` family `H(s)` of self-adjoint operators and a continuous eigenvalue `E(s)` separated from
the rest of the spectrum by a gap `g`, the circle `|z - E(s₀)| = g/2` works for all `s` near `s₀`,
so the eigenprojection is locally a parametric integral of the smooth resolvent and hence `C²`.
This removes the smoothness assumption on `P` from the adiabatic theorem.

## Main results

* `ring_inverse_sub_eq_sum`: the resolvent in the eigenbasis.
* `starProjection_ker_eq_sum`: the eigenprojection in the eigenbasis.
* `riesz_formula`: the Riesz formula.
* `eigenprojection_gap`: the gap estimate `g ‖v‖ ≤ ‖(T - E) v‖` for `v ⊥ ker (T - E)`.
* `contDiff_eigenprojection` (**smooth eigenprojections**).
* `adiabatic_of_gap` (**adiabatic theorem for a gapped eigenvalue**).
-/

namespace QM

open Complex Module Set
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

/-- The rank-one projection `|v⟩⟨v|`. -/
noncomputable def ketbra (v : E) : E →L[ℂ] E := (innerSL ℂ v).smulRight v

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
@[simp] lemma ketbra_apply (v x : E) : ketbra v x = inner ℂ v x • v := rfl

section Spectral

variable {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)

/-- The orthonormal eigenbasis of a self-adjoint operator. -/
noncomputable def eb : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E :=
  hT.isSymmetric.eigenvectorBasis rfl

/-- The eigenvalues of a self-adjoint operator. -/
noncomputable def el : Fin (finrank ℂ E) → ℝ := hT.isSymmetric.eigenvalues rfl

lemma apply_eb (k : Fin (finrank ℂ E)) : T (eb hT k) = (el hT k : ℂ) • eb hT k :=
  hT.isSymmetric.apply_eigenvectorBasis rfl k

lemma inner_eb_apply (k : Fin (finrank ℂ E)) (x : E) :
    inner ℂ (eb hT k) (T x) = (el hT k : ℂ) * inner ℂ (eb hT k) x := by
  rw [show inner ℂ (eb hT k) (T x) = inner ℂ (T (eb hT k)) x from (hT.isSymmetric (eb hT k) x).symm,
    apply_eb, inner_smul_left, Complex.conj_ofReal]

lemma sub_apply_eb (z : ℂ) (k : Fin (finrank ℂ E)) :
    (z • 1 - T) (eb hT k) = (z - el hT k) • eb hT k := by
  rw [_root_.sub_apply, _root_.smul_apply, _root_.one_apply_eq_self,
    apply_eb, sub_smul]

lemma sum_ketbra (x : E) : ∑ k, ketbra (eb hT k) x = x := by
  simp only [ketbra_apply]
  exact (eb hT).sum_repr' x

/-- The resolvent in the eigenbasis. -/
noncomputable def resolv (z : ℂ) : E →L[ℂ] E := ∑ k, (z - el hT k)⁻¹ • ketbra (eb hT k)

lemma resolv_spec {z : ℂ} (hz : ∀ k, z ≠ el hT k) :
    (z • 1 - T) * resolv hT z = 1 ∧ resolv hT z * (z • 1 - T) = 1 := by
  have hne : ∀ k, z - el hT k ≠ 0 := fun k => sub_ne_zero.mpr (hz k)
  constructor
  · ext x
    rw [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self]
    simp only [resolv, _root_.sum_apply, _root_.smul_apply, ketbra_apply,
      map_sum, map_smul, sub_apply_eb, smul_smul]
    conv_rhs => rw [← (eb hT).sum_repr' x]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    field_simp [hne k]
  · ext x
    simp only [resolv, _root_.mul_apply_eq_comp, _root_.sum_apply,
      _root_.smul_apply, ketbra_apply, _root_.one_apply_eq_self,
      _root_.sub_apply, inner_sub_right, inner_smul_right, inner_eb_apply, smul_smul]
    conv_rhs => rw [← (eb hT).sum_repr' x]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    field_simp [hne k]

/-- **The resolvent in the eigenbasis**: `(z - T)⁻¹ = Σ_k (z - λ_k)⁻¹ |e_k⟩⟨e_k|`. -/
theorem ring_inverse_sub_eq_sum {z : ℂ} (hz : ∀ k, z ≠ el hT k) :
    Ring.inverse (z • 1 - T) = resolv hT z := by
  obtain ⟨h1, h2⟩ := resolv_spec hT hz
  let u : (E →L[ℂ] E)ˣ := ⟨z • 1 - T, resolv hT z, h1, h2⟩
  change Ring.inverse (u : E →L[ℂ] E) = _
  rw [Ring.inverse_unit]
  rfl

lemma isUnit_sub {z : ℂ} (hz : ∀ k, z ≠ el hT k) : IsUnit (z • 1 - T) := by
  obtain ⟨h1, h2⟩ := resolv_spec hT hz
  exact isUnit_iff_exists.mpr ⟨_, h1, h2⟩

/-! ### The eigenprojection in the eigenbasis -/

lemma inner_eb_eq_zero_of_mem_ker {e : ℝ} {w : E}
    (hw : w ∈ LinearMap.ker ((T - (e : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) {k : Fin (finrank ℂ E)}
    (hk : el hT k ≠ e) : inner ℂ (eb hT k) w = 0 := by
  have hTw : T w = (e : ℂ) • w := by
    have := LinearMap.mem_ker.mp hw
    simpa [sub_eq_zero] using this
  have h := inner_eb_apply hT k w
  rw [hTw, inner_smul_right] at h
  have h2 : ((el hT k : ℂ) - e) * inner ℂ (eb hT k) w = 0 := by rw [sub_mul, ← h, sub_self]
  have hne : (el hT k : ℂ) - e ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hk
  exact (mul_eq_zero.mp h2).resolve_left hne

/-- **The eigenprojection in the eigenbasis**: the orthogonal projection onto `ker (T - E)` is
`Σ_{λ_k = E} |e_k⟩⟨e_k|`. -/
theorem starProjection_ker_eq_sum (e : ℝ) :
    (LinearMap.ker ((T - (e : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)).starProjection =
      ∑ k ∈ Finset.univ.filter (fun k => el hT k = e), ketbra (eb hT k) := by
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [_root_.sum_apply]
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [ketbra_apply]
    refine Submodule.smul_mem _ _ (LinearMap.mem_ker.mpr ?_)
    have hk' : el hT k = e := (Finset.mem_filter.mp hk).2
    change (T - (e : ℂ) • 1) (eb hT k) = 0
    rw [_root_.sub_apply, apply_eb, _root_.smul_apply,
      _root_.one_apply_eq_self, hk', sub_self]
  · intro w hw
    have hx : x - (∑ k ∈ Finset.univ.filter (fun k => el hT k = e), ketbra (eb hT k)) x =
        ∑ k ∈ Finset.univ.filter (fun k => ¬ el hT k = e), inner ℂ (eb hT k) x • eb hT k := by
      have h := (eb hT).sum_repr' x
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => el hT k = e)] at h
      rw [_root_.sum_apply]
      simp only [ketbra_apply]
      nth_rewrite 1 [← h]
      abel
    rw [hx, sum_inner]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [inner_smul_left, inner_eb_eq_zero_of_mem_ker hT hw (Finset.mem_filter.mp hk).2, mul_zero]

/-! ### The Riesz formula -/

lemma integral_sub_inv_eq {c w : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w - c‖ ≠ R) :
    (∮ z in C(c, R), (z - w)⁻¹) = if ‖w - c‖ < R then 2 * π * I else 0 := by
  split_ifs with h
  · exact circleIntegral.integral_sub_inv_of_mem_ball (by rwa [Metric.mem_ball, dist_eq_norm])
  · have hlt : R < ‖w - c‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hw)
    refine DiffContOnCl.circleIntegral_eq_zero hR.le ?_
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hR.ne']
    intro z hz
    have hzw : z - w ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [Metric.mem_closedBall, dist_eq_norm, h0] at hz
      linarith
    exact ((differentiableAt_id.sub_const w).inv hzw).differentiableWithinAt

/-- The contour integral of the resolvent. -/
theorem circleIntegral_resolvent {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hk : ∀ k, ‖(el hT k : ℂ) - c‖ ≠ R) :
    (∮ z in C(c, R), Ring.inverse (z • 1 - T)) =
      ∑ k, (if ‖(el hT k : ℂ) - c‖ < R then 2 * π * I else 0) • ketbra (eb hT k) := by
  have hne : ∀ z ∈ Metric.sphere c R, ∀ k, z ≠ el hT k := by
    intro z hz k h
    rw [mem_sphere_iff_norm, h] at hz
    exact hk k hz
  rw [circleIntegral.integral_congr hR.le (g := fun z => ∑ k, (z - el hT k)⁻¹ • ketbra (eb hT k))
    (fun z hz => ring_inverse_sub_eq_sum hT (hne z hz))]
  rw [circleIntegral.integral_fun_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [circleIntegral.integral_smul_const, integral_sub_inv_eq hR (hk k)]
  · intro k _
    refine ContinuousOn.circleIntegrable hR.le ?_
    have h1 : ContinuousOn (fun z : ℂ => (z - el hT k)⁻¹) (Metric.sphere c R) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.mpr (hne z hz k)
    exact h1.smul (continuousOn_const (c := ketbra (eb hT k)))

/-- **The Riesz formula**: if the circle `|z - c| = R` encloses the eigenvalue `E` and no other
eigenvalue, then `(2πi)⁻¹ ∮ (z - T)⁻¹ dz` is the orthogonal projection onto `ker (T - E)`. -/
theorem riesz_formula {c : ℂ} {R : ℝ} (hR : 0 < R) {e : ℝ} (hin : ‖(e : ℂ) - c‖ < R)
    (hout : ∀ k, el hT k ≠ e → R < ‖(el hT k : ℂ) - c‖) :
    (2 * π * I)⁻¹ • (∮ z in C(c, R), Ring.inverse (z • 1 - T)) =
      (LinearMap.ker ((T - (e : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)).starProjection := by
  have hiff : ∀ k, ‖(el hT k : ℂ) - c‖ < R ↔ el hT k = e := by
    intro k
    constructor
    · intro h
      by_contra hne
      exact absurd h (not_lt.mpr (hout k hne).le)
    · intro h; rw [h]; exact hin
  have hk : ∀ k, ‖(el hT k : ℂ) - c‖ ≠ R := by
    intro k
    by_cases h : el hT k = e
    · exact ((hiff k).mpr h).ne
    · exact (hout k h).ne'
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [circleIntegral_resolvent hT hR hk, starProjection_ker_eq_sum hT e, Finset.smul_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  by_cases h : el hT k = e
  · rw [ite_eq_left ((hiff k).mpr h), ite_eq_left h, inv_mul_cancel₀ h2pi, one_smul]
  · rw [ite_eq_right (fun h' => h ((hiff k).mp h')), ite_eq_right h, mul_zero, zero_smul]

/-- **The gap estimate**: if every eigenvalue is `E` or at distance at least `g ≥ 0` from `E`,
then `g ‖v‖ ≤ ‖(T - E) v‖` for every `v` with `P v = 0`. -/
theorem eigenprojection_gap {e g : ℝ} (hg : 0 ≤ g) (hgap : ∀ k, el hT k = e ∨ g ≤ |el hT k - e|)
    {v : E}
    (hv : (LinearMap.ker ((T - (e : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)).starProjection v = 0) :
    g * ‖v‖ ≤ ‖(T - (e : ℂ) • 1) v‖ := by
  rw [starProjection_ker_eq_sum hT e, _root_.sum_apply] at hv
  have hzero : ∀ j, el hT j = e → inner ℂ (eb hT j) v = 0 := by
    intro j hj
    have h := congrArg (inner ℂ (eb hT j)) hv
    rw [inner_zero_right, inner_sum] at h
    rw [← h, Finset.sum_eq_single j]
    · rw [ketbra_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, (eb hT).orthonormal.1 j]
      simp
    · intro k _ hkj
      rw [ketbra_apply, inner_smul_right, (eb hT).orthonormal.2 (Ne.symm hkj), mul_zero]
    · intro hj'; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hj'
  have hcoef : ∀ k, inner ℂ (eb hT k) ((T - (e : ℂ) • 1) v) =
      ((el hT k : ℂ) - e) * inner ℂ (eb hT k) v := by
    intro k
    rw [_root_.sub_apply, inner_sub_right, inner_eb_apply,
      _root_.smul_apply, _root_.one_apply_eq_self, inner_smul_right, sub_mul]
  have hsq : (g * ‖v‖) ^ 2 ≤ ‖(T - (e : ℂ) • 1) v‖ ^ 2 := by
    rw [← (eb hT).sum_sq_norm_inner_right, mul_pow, ← (eb hT).sum_sq_norm_inner_right,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hcoef, norm_mul, mul_pow]
    rcases hgap k with h | h
    · rw [hzero k h]; simp
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have : ‖((el hT k : ℂ) - e)‖ = |el hT k - e| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [this]
      exact pow_le_pow_left₀ hg h 2
  exact le_of_sq_le_sq (by simpa [abs_of_nonneg (mul_nonneg hg (norm_nonneg v))] using hsq)
    (norm_nonneg _)

end Spectral

/-! ### Smoothness of the eigenprojection -/

/-- The eigenprojection `P(s)` onto `ker (H(s) - E(s))`. -/
noncomputable def eigenproj (H : ℝ → E →L[ℂ] E) (Ev : ℝ → ℝ) (s : ℝ) : E →L[ℂ] E :=
  (LinearMap.ker ((H s - (Ev s : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)).starProjection

lemma norm_ofReal_sub (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Smooth eigenprojections.** Let `H(s)` be a `C²` family of self-adjoint operators and `E(s)` a
continuous function such that every eigenvalue of `H(s)` is `E(s)` or at distance at least `g > 0`
from `E(s)`. Then the eigenprojection onto `ker (H(s) - E(s))` is a `C²` function of `s`. -/
theorem contDiff_eigenproj {H : ℝ → E →L[ℂ] E} (hH : ContDiff ℝ 2 H)
    (hsa : ∀ s, IsSelfAdjoint (H s)) {Ev : ℝ → ℝ} (hEv : Continuous Ev) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ s (lam : ℝ) (v : E), v ≠ 0 → H s v = (lam : ℂ) • v → lam = Ev s ∨ g ≤ |lam - Ev s|) :
    ContDiff ℝ 2 (eigenproj H Ev) := by
  have hgapk : ∀ s k, el (hsa s) k = Ev s ∨ g ≤ |el (hsa s) k - Ev s| := fun s k =>
    hgap s _ _ ((eb (hsa s)).orthonormal.ne_zero k) (apply_eb (hsa s) k)
  rw [contDiff_iff_contDiffAt]
  intro s₀
  set c : ℂ := ((Ev s₀ : ℝ) : ℂ)
  set R : ℝ := g / 2
  have hR : 0 < R := by positivity
  have hRdef : R = g / 2 := rfl
  set u : Set ℝ := {s | |Ev s - Ev s₀| < g / 4}
  have hu : IsOpen u := isOpen_lt ((hEv.sub continuous_const).abs) continuous_const
  have hs₀ : s₀ ∈ u := by
    change |Ev s₀ - Ev s₀| < g / 4
    rw [sub_self, abs_zero]; positivity
  have hin : ∀ s ∈ u, ‖(Ev s : ℂ) - c‖ < R := fun s hs => by
    rw [norm_ofReal_sub, hRdef]; have : |Ev s - Ev s₀| < g / 4 := hs; linarith
  have hout : ∀ s ∈ u, ∀ k, el (hsa s) k ≠ Ev s → R < ‖(el (hsa s) k : ℂ) - c‖ := by
    intro s hs k hk
    have hs' : |Ev s - Ev s₀| < g / 4 := hs
    rcases hgapk s k with h | h
    · exact absurd h hk
    · rw [norm_ofReal_sub, hRdef]
      have := abs_sub_abs_le_abs_sub (el (hsa s) k - Ev s) (Ev s₀ - Ev s)
      have e : el (hsa s) k - Ev s - (Ev s₀ - Ev s) = el (hsa s) k - Ev s₀ := by ring
      rw [e, abs_sub_comm (Ev s₀)] at this
      linarith
  have hne : ∀ s ∈ u, ∀ θ : ℝ, ∀ k, circleMap c R θ ≠ el (hsa s) k := by
    intro s hs θ k h
    have hz : ‖circleMap c R θ - c‖ = R := by
      rw [← dist_eq_norm]; exact (circleMap_mem_sphere c hR.le θ)
    rw [h] at hz
    by_cases hk : el (hsa s) k = Ev s
    · rw [hk] at hz; exact (hin s hs).ne hz
    · exact (hout s hs k hk).ne' hz
  -- the parametric integral
  set f : ℝ → ℝ → E →L[ℂ] E := fun s θ =>
    deriv (circleMap c R) θ • Ring.inverse (circleMap c R θ • (1 : E →L[ℂ] E) - H s)
  have hf : ContDiffOn ℝ 2 (Function.uncurry f) (u ×ˢ uIcc 0 (2 * π)) := by
    rintro ⟨s, θ⟩ ⟨hs, -⟩
    apply ContDiffAt.contDiffWithinAt
    have hunit : IsUnit (circleMap c R θ • (1 : E →L[ℂ] E) - H s) :=
      isUnit_sub (hsa s) (hne s hs θ)
    have h1 : ContDiffAt ℝ 2 (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E))
        (circleMap c R θ • (1 : E →L[ℂ] E) - H s) := by
      have := contDiffAt_ringInverse (n := 2) ℝ hunit.unit
      rwa [IsUnit.unit_spec] at this
    have hg2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => circleMap c R p.2 • (1 : E →L[ℂ] E) - H p.1) :=
      (((contDiff_circleMap c R).comp contDiff_snd).smul contDiff_const).sub
        (hH.comp contDiff_fst)
    have hd : ContDiff ℝ 2 (fun p : ℝ × ℝ => deriv (circleMap c R) p.2) := by
      simp_rw [deriv_circleMap]
      exact ((contDiff_circleMap 0 R).comp contDiff_snd).mul contDiff_const
    have h2 := h1.comp (s, θ) hg2.contDiffAt
    exact hd.contDiffAt.smul h2
  have hF : ContDiffOn ℝ 2 (fun s => (2 * π * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, f s θ) u :=
    (hf.parametric_intervalIntegral (μ := MeasureTheory.volume) hu).const_smul _
  refine (hF.contDiffAt (hu.mem_nhds hs₀)).congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hs₀] with s hs
  rw [eigenproj, ← riesz_formula (hsa s) hR (hin s hs) (hout s hs)]
  rfl

omit [FiniteDimensional ℂ E] in
/-- The eigenprojection satisfies `H P = E P`. -/
lemma mul_eigenproj (H : ℝ → E →L[ℂ] E) (Ev : ℝ → ℝ) (s : ℝ) :
    H s * eigenproj H Ev s = (Ev s : ℂ) • eigenproj H Ev s := by
  ext x
  have hm := Submodule.starProjection_apply_mem
    (LinearMap.ker ((H s - (Ev s : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) x
  have h0 := LinearMap.mem_ker.mp hm
  change (H s - (Ev s : ℂ) • 1) (eigenproj H Ev s x) = 0 at h0
  rw [_root_.sub_apply, sub_eq_zero] at h0
  rw [_root_.mul_apply_eq_comp, h0]
  rfl

/-- **The adiabatic theorem for a gapped eigenvalue.** Let `H(s)` be a `C²` family of self-adjoint
operators and `E(s)` a `C¹` eigenvalue separated from the rest of the spectrum by a gap `g > 0`.
With `P(s)` the eigenprojection onto `ker (H(s) - E(s))`, there is `C` such that
`‖(1 - P(1)) U_ε(1) P(0)‖ ≤ C ε` for every `ε > 0`. -/
theorem adiabatic_of_gap {H : ℝ → E →L[ℂ] E} (hH : ContDiff ℝ 2 H)
    (hsa : ∀ s, IsSelfAdjoint (H s)) {Ev : ℝ → ℝ} (hEv : ContDiff ℝ 1 Ev) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ s (lam : ℝ) (v : E), v ≠ 0 → H s v = (lam : ℂ) • v → lam = Ev s ∨ g ≤ |lam - Ev s|) :
    ∃ C, ∀ ε > 0, ∀ U, IsPropagator H ε U →
      ‖(1 - eigenproj H Ev 1) * U 1 * eigenproj H Ev 0‖ ≤ C * ε := by
  have hgapk : ∀ s k, el (hsa s) k = Ev s ∨ g ≤ |el (hsa s) k - Ev s| := fun s k =>
    hgap s _ _ ((eb (hsa s)).orthonormal.ne_zero k) (apply_eb (hsa s) k)
  exact adiabatic (hH.of_le (by norm_num)) hsa hEv
    (contDiff_eigenproj hH hsa hEv.continuous hg hgap)
    (fun s => isStarProjection_starProjection) (mul_eigenproj H Ev) hg
    (fun s _ v hv => eigenprojection_gap (hsa s) hg.le (hgapk s) hv)

end QM
